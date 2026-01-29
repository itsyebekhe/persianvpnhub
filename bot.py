import asyncio
import json
import os
import re
import logging
import base64
import ipaddress
import socket
import hashlib
import shutil
from datetime import datetime, timezone, timedelta
from urllib.parse import urlparse, parse_qs, unquote

import aiohttp
import geoip2.database
from telethon import TelegramClient, Button
from telethon.sessions import StringSession

# --- Configuration ---
API_ID = int(os.environ.get("API_ID"))
API_HASH = os.environ.get("API_HASH")
SESSION_STRING = os.environ.get("SESSION_STRING")
BOT_TOKEN = os.environ.get("BOT_TOKEN")
DESTINATION_ID = int(os.environ.get("DESTINATION_ID"))
CHANNEL_LINK = "https://t.me/persianvpnhub"

# File Paths
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CHANNELS_FILE = os.path.join(BASE_DIR, 'channelsData', 'channelsAssets.json')
HISTORY_FILE = os.path.join(BASE_DIR, 'history.json')
GEOIP_DB = os.path.join(BASE_DIR, 'Country.mmdb')
TEMP_DIR = os.path.join(BASE_DIR, 'temp_downloads')

# URLs
GEOIP_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
CF_RANGES_URL = "https://raw.githubusercontent.com/ircfspace/cf-ip-ranges/refs/heads/main/export.ipv4"

# Constants
CHECK_LIMIT_PER_CHANNEL = 3
DEDUPE_HOURS = 72
TIMEOUT_TCP = 2

# Regex & Extensions
VMESS_REGEX = r'(vmess|vless|trojan|ss|tuic|hysteria2?):\/\/[^\s\n]+'
MTPROTO_REGEX = r'(tg:\/\/proxy\?|https:\/\/t\.me\/proxy\?)[^\s\n]+'
NPV_EXTENSIONS = ('.npvt')

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# --- JALALI CONVERTER (Native Python Implementation) ---
class JalaliConverter:
    @staticmethod
    def gregorian_to_jalali(gy, gm, gd):
        g_d_m = [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334]
        if (gy > 1600):
            jy = 979
            gy -= 1600
        else:
            jy = 0
            gy -= 621
        
        days = (365 * gy) + ((gy + 1) // 4) - ((gy + 99) // 100) + ((gy + 399) // 400) - 80 + gd + g_d_m[gm - 1]
        jy += 33 * (days // 12053)
        days %= 12053
        jy += 4 * (days // 1461)
        days %= 1461
        if (days > 365):
            jy += (days - 1) // 365
            days = (days - 1) % 365
        if (days < 186):
            jm = 1 + (days // 31)
            jd = 1 + (days % 31)
        else:
            jm = 7 + ((days - 186) // 30)
            jd = 1 + ((days - 186) % 30)
        return (jy, jm, jd)

    @staticmethod
    def get_persian_time(timestamp):
        # Convert UTC to Iran Standard Time (UTC+03:30)
        utc_dt = datetime.fromtimestamp(timestamp, timezone.utc)
        tehran_dt = utc_dt + timedelta(hours=3, minutes=30)
        
        jy, jm, jd = JalaliConverter.gregorian_to_jalali(tehran_dt.year, tehran_dt.month, tehran_dt.day)
        return f"{tehran_dt.hour:02d}:{tehran_dt.minute:02d} - {jy}/{jm:02d}/{jd:02d}"

# --- CLOUDFLARE ---
CF_IPV6_DEFAULTS = [
    "2400:cb00::/32", "2606:4700::/32", "2803:f800::/32", "2405:b500::/32",
    "2405:8100::/32", "2a06:98c0::/29", "2c0f:f248::/32"
]

class CloudflareManager:
    def __init__(self):
        self.networks = []
        for cidr in CF_IPV6_DEFAULTS:
            try: self.networks.append(ipaddress.ip_network(cidr))
            except: pass

    async def update_ranges(self):
        logger.info("Fetching Cloudflare IPv4 ranges...")
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(CF_RANGES_URL, timeout=10) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        lines = text.splitlines()
                        count = 0
                        for line in lines:
                            line = line.strip()
                            if not line or line.startswith('#'): continue
                            try:
                                self.networks.append(ipaddress.ip_network(line))
                                count += 1
                            except ValueError:
                                pass
                        logger.info(f"Loaded {count} Cloudflare IPv4 ranges.")
                    else:
                        logger.warning(f"Failed to fetch CF ranges. Status: {resp.status}")
        except Exception as e:
            logger.error(f"Error updating Cloudflare ranges: {e}")

    def is_cloudflare(self, ip_str):
        if not ip_str: return False
        try:
            clean_ip = ip_str.strip('[]')
            ip_obj = ipaddress.ip_address(clean_ip)
            for net in self.networks:
                if ip_obj in net:
                    return True
        except ValueError:
            return False
        return False

class ConfigNormalizer:
    @staticmethod
    def normalize(content, proto):
        try:
            data = {}
            if proto == 'vmess':
                raw = content.replace('vmess://', '')
                padding = len(raw) % 4
                if padding: raw += "=" * (4 - padding)
                json_str = base64.b64decode(raw).decode('utf-8', errors='ignore')
                data = json.loads(json_str)
                for k in ['ps', 'remarks', 'id']:
                    data.pop(k, None)
            
            elif proto in ['vless', 'trojan', 'tuic', 'hysteria', 'ss', 'hysteria2']:
                parsed = urlparse(content)
                host_port = parsed.netloc.split('@')[-1]
                params = parse_qs(parsed.query)
                flat_params = {k: v[0] for k, v in params.items()}
                for key in ['fp', 'pbk', 'sid', 'spx']:
                    flat_params.pop(key, None)
                
                data = {
                    'protocol': proto,
                    'host_port': host_port,
                    'path': parsed.path,
                    'params': flat_params
                }

            elif proto == 'mtproto':
                parsed = urlparse(content.replace('tg://', 'http://'))
                params = parse_qs(parsed.query)
                data = {
                    'protocol': 'mtproto',
                    'server': params.get('server', [''])[0],
                    'port': params.get('port', [''])[0]
                }

            if not data: return content
            return json.dumps(data, sort_keys=True)
        except:
            return content

class ConfigManager:
    def __init__(self):
        self.history = {}
        self.load_history()
        self.geo_reader = None
        self.cf_manager = CloudflareManager()
        self.dns_cache = {}
        if not os.path.exists(TEMP_DIR): os.makedirs(TEMP_DIR)

    def load_history(self):
        if os.path.exists(HISTORY_FILE):
            try:
                with open(HISTORY_FILE, 'r') as f:
                    self.history = json.load(f)
            except: self.history = {}
        
        current_time = datetime.now(timezone.utc).timestamp()
        cutoff = current_time - (DEDUPE_HOURS * 3600)
        self.history = {k: v for k, v in self.history.items() if v > cutoff}

    def save_history(self):
        with open(HISTORY_FILE, 'w') as f: json.dump(self.history, f)

    def is_duplicate(self, unique_str):
        fingerprint = hashlib.sha256(unique_str.encode('utf-8')).hexdigest()
        if fingerprint in self.history: return True
        self.history[fingerprint] = datetime.now(timezone.utc).timestamp()
        return False

    async def setup_external_resources(self):
        if not os.path.exists(GEOIP_DB) or (datetime.now().timestamp() - os.path.getmtime(GEOIP_DB) > 86400):
            logger.info("Downloading GeoIP...")
            async with aiohttp.ClientSession() as session:
                async with session.get(GEOIP_URL) as resp:
                    if resp.status == 200:
                        with open(GEOIP_DB, 'wb') as f: f.write(await resp.read())
        try: self.geo_reader = geoip2.database.Reader(GEOIP_DB)
        except: pass
        await self.cf_manager.update_ranges()

    async def resolve_dns(self, host):
        if not host: return None
        try:
            ipaddress.ip_address(host.strip('[]'))
            return host.strip('[]')
        except ValueError:
            pass

        if host in self.dns_cache: return self.dns_cache[host]
        try:
            loop = asyncio.get_running_loop()
            ip = await loop.run_in_executor(None, socket.gethostbyname, host)
            self.dns_cache[host] = ip
            return ip
        except:
            return None

    def get_location_info(self, ip_str):
        # 1. Cloudflare Check (Prioritized)
        if self.cf_manager.is_cloudflare(ip_str):
            return "☁️", "کلودفلر"
        
        # 2. GeoIP Check
        if not self.geo_reader or not ip_str: return "🏁", "نامشخص"
        try:
            resp = self.geo_reader.country(ip_str)
            iso = resp.country.iso_code
            name = resp.country.names.get('en', 'Unknown')
            
            persian_names = {
                'Germany': 'آلمان', 'United States': 'آمریکا', 'Netherlands': 'هلند',
                'France': 'فرانسه', 'United Kingdom': 'انگلیس', 'Finland': 'فنلاند',
                'Canada': 'کانادا', 'Turkey': 'ترکیه', 'Russia': 'روسیه',
                'Singapore': 'سنگاپور', 'Japan': 'ژاپن', 'Sweden': 'سوئد',
                'United Arab Emirates': 'امارات', 'Switzerland': 'سوئیس',
                'Poland': 'لهستان', 'Italy': 'ایتالیا', 'Spain': 'اسپانیا',
                'Ireland': 'ایرلند', 'Belgium': 'بلژیک', 'Ukraine': 'اوکراین'
            }
            display_name = persian_names.get(name, name)
            flag = chr(127397 + ord(iso[0])) + chr(127397 + ord(iso[1])) if iso else "🏁"
            return flag, display_name
        except: return "🏁", "نامشخص"

    @staticmethod
    def parse_config_details(config_str, proto):
        host = None
        port = None
        try:
            if proto == 'vmess':
                b64 = config_str[8:]
                padding = len(b64) % 4
                if padding: b64 += "=" * (4 - padding)
                data = json.loads(base64.b64decode(b64).decode('utf-8', errors='ignore'))
                host = data.get('add')
                port = data.get('port')
            elif proto == 'mtproto':
                parsed = urlparse(config_str.replace('tg://', 'http://'))
                params = parse_qs(parsed.query)
                host = params.get('server', [None])[0]
                port = params.get('port', [None])[0]
            else:
                parsed = urlparse(config_str)
                host = parsed.hostname
                port = parsed.port
            
            return host, int(port) if port else None
        except Exception:
            return None, None

    @staticmethod
    async def check_connection(ip, port):
        if not ip or not port: return False
        try:
            conn = asyncio.open_connection(ip, port)
            reader, writer = await asyncio.wait_for(conn, timeout=TIMEOUT_TCP)
            writer.close()
            await writer.wait_closed()
            return True
        except: return False

    @staticmethod
    def calculate_file_hash(file_path):
        hash_sha = hashlib.sha256()
        with open(file_path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_sha.update(chunk)
        return hash_sha.hexdigest()

async def main():
    logger.info("Starting PSG Collector Bot...")
    
    manager = ConfigManager()
    await manager.setup_external_resources()
    
    user_client = TelegramClient(StringSession(SESSION_STRING), API_ID, API_HASH)
    bot_client = TelegramClient('bot_session', API_ID, API_HASH)
    
    await user_client.connect()
    await bot_client.start(bot_token=BOT_TOKEN)

    try:
        with open(CHANNELS_FILE, 'r', encoding='utf-8') as f:
            sources = json.load(f)
    except: return

    # --- PHASE 1: COLLECT ---
    logger.info("Phase 1: Collecting...")
    collected_items = []
    for channel_username in sources.keys():
        try:
            entity = await user_client.get_entity(channel_username)
            async for message in user_client.iter_messages(entity, limit=CHECK_LIMIT_PER_CHANNEL):
                ts = message.date.astimezone(timezone.utc).timestamp()
                
                # Files
                if message.file and message.file.name and message.file.name.lower().endswith(NPV_EXTENSIONS):
                    collected_items.append({'ts': ts, 'type': 'file', 'msg_obj': message, 'source': channel_username})
                    continue

                # Text
                if message.text:
                    text = message.text
                    for match in re.finditer(VMESS_REGEX, text, re.IGNORECASE):
                        collected_items.append({'ts': ts, 'type': 'text', 'proto': match.group(1), 'raw': match.group(0), 'source': channel_username})
                    for match in re.finditer(MTPROTO_REGEX, text, re.IGNORECASE):
                        collected_items.append({'ts': ts, 'type': 'text', 'proto': 'mtproto', 'raw': match.group(0), 'source': channel_username})

        except Exception as e:
            logger.warning(f"Error scraping {channel_username}: {e}")

    # --- PHASE 2: SORT ---
    collected_items.sort(key=lambda x: x['ts'])

    # --- PHASE 3: PROCESS ---
    logger.info(f"Phase 3: Processing {len(collected_items)} items...")
    processed_count = 0
    for item in collected_items:
        try:
            # Common Data
            shamsi_date = JalaliConverter.get_persian_time(item['ts'])
            
            # --- TEXT CONFIGS ---
            if item['type'] == 'text':
                config_str = item['raw']
                proto = item['proto']
                
                # Normalize & Deduplicate
                norm_json = ConfigNormalizer.normalize(config_str, proto)
                if not norm_json or manager.is_duplicate(norm_json): continue

                # Check Connection
                host, port = manager.parse_config_details(config_str, proto)
                if not host: continue
                ip = await manager.resolve_dns(host)
                if not ip: continue
                if not await manager.check_connection(ip, port): continue

                # Get Info
                flag, country = manager.get_location_info(ip)
                clean_proto = proto.upper()
                if clean_proto == 'VMESS': clean_proto = 'VMess'
                if clean_proto == 'VLESS': clean_proto = 'VLESS'

                caption = (
                    f"📂 کانفیگ {clean_proto}\n"
                    f"{flag} پینگ: متصل (TCP)\n\n"
                    f"🕒 انتشار: {shamsi_date}\n"
                    f"💡 منبع: @{item['source']}\n"
                )
                
                final_msg = f"{caption}\n```{config_str}```"

                # Buttons
                buttons = []
                if proto == 'mtproto': 
                    buttons.append([Button.url("⚡️ اتصال (Connect)", config_str)])
                # Add "More Configs" Button to all text posts
                buttons.append([Button.url("🔍 دریافت کانفیگ‌های بیشتر", CHANNEL_LINK)])

                await bot_client.send_message(
                    DESTINATION_ID, 
                    final_msg, 
                    buttons=buttons,
                    link_preview=False
                )
                processed_count += 1
                await asyncio.sleep(4)

            # --- FILE CONFIGS ---
            elif item['type'] == 'file':
                msg = item['msg_obj']
                path = await msg.download_media(file=TEMP_DIR)
                if not path: continue

                file_hash = manager.calculate_file_hash(path)
                if manager.is_duplicate(file_hash):
                    os.remove(path); continue
                
                caption = (
                    f"📂 فایل کانفیگ NapsternetV\n"
                    f"🏁 پینگ: نامشخص\n\n"
                    f"🕒 انتشار: {shamsi_date}\n"
                    f"💡 منبع: @{item['source']}\n"
                )
                
                # Add "More Configs" Button to files
                buttons = [[Button.url("کانفیگ های بیشتر", CHANNEL_LINK)]]
                
                await bot_client.send_file(
                    DESTINATION_ID, 
                    path, 
                    caption=caption,
                    buttons=buttons
                )
                processed_count += 1
                if os.path.exists(path): os.remove(path)
                await asyncio.sleep(4)

        except Exception as e:
            logger.error(f"Error processing item: {e}")

    if os.path.exists(TEMP_DIR): shutil.rmtree(TEMP_DIR)
    manager.save_history()
    logger.info(f"Finished. Posted {processed_count} new.")
    
    await user_client.disconnect()
    await bot_client.disconnect()

if __name__ == '__main__':
    asyncio.run(main())
