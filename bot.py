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
import time
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
STATS_FILE = os.path.join(BASE_DIR, 'stats.json')
GEOIP_DB = os.path.join(BASE_DIR, 'Country.mmdb')
TEMP_DIR = os.path.join(BASE_DIR, 'temp_downloads')

# Subscription Files
SUB_FILE_NORMAL = os.path.join(BASE_DIR, 'normal')
SUB_FILE_B64 = os.path.join(BASE_DIR, 'base64')

# URLs
GEOIP_URL = "https://github.com/P3TERX/GeoLite.mmdb/raw/download/GeoLite2-Country.mmdb"
CF_RANGES_URL = "https://raw.githubusercontent.com/ircfspace/cf-ip-ranges/refs/heads/main/export.ipv4"

# Constants
CHECK_LIMIT_PER_CHANNEL = 5
DEDUPE_HOURS = 72  # This is the 72 hours setting
TIMEOUT_TCP = 2
FETCH_DELAY = 6

# Regex & Extensions
VMESS_REGEX = r'(vmess|vless|trojan|ss|tuic|hysteria2?):\/\/[^\s\n]+'
MTPROTO_REGEX = r'(?:tg:\/\/|https:\/\/t\.me\/)proxy\?(?=[^"\'\s<>]*server=)(?=[^"\'\s<>]*port=)([^"\'\s<>]+)'
NPV_EXTENSIONS = ('.npvt')

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# --- JALALI CONVERTER ---
class JalaliConverter:
    @staticmethod
    def gregorian_to_jalali(gy, gm, gd):
        g_days_in_month = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
        j_days_in_month = [31, 31, 31, 31, 31, 31, 30, 30, 30, 30, 30, 29]

        gy -= 1600
        jy = 979

        # Calculate total Gregorian days passed
        g_day_no = 365 * gy + (gy + 3) // 4 - (gy + 99) // 100 + (gy + 399) // 400

        for i in range(gm - 1):
            g_day_no += g_days_in_month[i]

        # Check for leap year to add the extra day after Feb
        if gm > 2 and ((gy + 1600) % 4 == 0 and (gy + 1600) % 100 != 0 or (gy + 1600) % 400 == 0):
            g_day_no += 1

        g_day_no += gd - 1

        j_day_no = g_day_no - 79

        j_np = j_day_no // 12053
        j_day_no %= 12053

        jy += 33 * j_np + 4 * (j_day_no // 1461)

        j_day_no %= 1461

        if j_day_no >= 366:
            jy += (j_day_no - 1) // 365
            j_day_no = (j_day_no - 1) % 365

        for i in range(11):
            if j_day_no < j_days_in_month[i]:
                jm = i + 1
                jd = j_day_no + 1
                break
            j_day_no -= j_days_in_month[i]
        else:
            jm = 12
            jd = j_day_no + 1

        return jy, jm, jd

    @staticmethod
    def get_persian_time(timestamp):
        utc_dt = datetime.fromtimestamp(timestamp, timezone.utc)
        # Iran Standard Time is UTC+3:30 (DST is no longer observed in Iran)
        tehran_dt = utc_dt + timedelta(hours=3, minutes=30)
        jy, jm, jd = JalaliConverter.gregorian_to_jalali(tehran_dt.year, tehran_dt.month, tehran_dt.day)
        return f"{tehran_dt.hour:02d}:{tehran_dt.minute:02d} - {jy}/{jm:02d}/{jd:02d}"
    
    @staticmethod
    def get_jalali_date_from_str(date_str):
        try:
            dt = datetime.strptime(date_str, '%Y-%m-%d')
            jy, jm, jd = JalaliConverter.gregorian_to_jalali(dt.year, dt.month, dt.day)
            return f"{jy}/{jm:02d}/{jd:02d}"
        except:
            return date_str

# --- SUBSCRIPTION MANAGER ---

REPO_USER = "itsyebekhe" 
REPO_NAME = "persianvpnhub"
EXPORT_BRANCH = "export"
EXISTING_SUBS_URL = f"https://raw.githubusercontent.com/{REPO_USER}/{REPO_NAME}/{EXPORT_BRANCH}/normal"

class SubscriptionManager:
    def __init__(self):
        self.normal_path = SUB_FILE_NORMAL
        self.b64_path = SUB_FILE_B64
        self.load_remote_subs()

    def load_remote_subs(self):
        """Downloads the current subscription file from the export branch."""
        if os.path.exists(self.normal_path):
            return # If file exists locally (manual run), don't overwrite

        logger.info(f"Downloading existing subs from {EXPORT_BRANCH} branch...")
        try:
            import requests # Make sure to import requests or use aiohttp
            response = requests.get(EXISTING_SUBS_URL, timeout=10)
            if response.status_code == 200:
                with open(self.normal_path, 'w', encoding='utf-8') as f:
                    f.write(response.text)
                logger.info("Successfully loaded existing subscriptions.")
            else:
                logger.warning("Could not download existing subs (might be first run or branch empty).")
                # Create empty file
                open(self.normal_path, 'a').close()
        except Exception as e:
            logger.error(f"Failed to load remote subs: {e}")
            open(self.normal_path, 'a').close()
            
    def trim_files(self):
        """
        Removes the first half of the subscription file (oldest configs).
        Keeps the most recent 50%.
        """
        logger.info("New day detected: Trimming subscription files (removing oldest 50%).")
        
        if not os.path.exists(self.normal_path):
            return

        try:
            with open(self.normal_path, 'r', encoding='utf-8') as f:
                content = f.read().strip()
            
            if not content:
                return

            lines = content.split('\n')
            total_lines = len(lines)
            
            # Keep the last 50%
            if total_lines > 1:
                keep_start_index = total_lines // 2
                new_lines = lines[keep_start_index:]
            else:
                new_lines = lines # Keep if only 1 line

            new_content = "\n".join(new_lines)

            # Write Normal File
            with open(self.normal_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            
            # Write Base64 File
            b64_content = base64.b64encode(new_content.encode('utf-8')).decode('utf-8')
            with open(self.b64_path, 'w', encoding='utf-8') as f:
                f.write(b64_content)
                
            logger.info(f"Trimmed subscription: {total_lines} -> {len(new_lines)} lines.")
            
        except Exception as e:
            logger.error(f"Error trimming subscription files: {e}")

    def update_subscription(self, new_configs):
        """Appends new configs to files and updates Base64."""
        if not new_configs:
            return

        # Read existing content
        existing_content = ""
        if os.path.exists(self.normal_path):
            with open(self.normal_path, 'r', encoding='utf-8') as f:
                existing_content = f.read()

        # Prepare content to append
        # Ensure we start on a new line if file wasn't empty
        separator = "\n" if existing_content.strip() else ""
        to_add = separator + "\n".join(new_configs)
        
        full_content = existing_content + to_add
        
        # Write Normal File
        with open(self.normal_path, 'w', encoding='utf-8') as f:
            f.write(full_content)
        
        # Write Base64 File
        b64_content = base64.b64encode(full_content.encode('utf-8')).decode('utf-8')
        with open(self.b64_path, 'w', encoding='utf-8') as f:
            f.write(b64_content)
        
        logger.info(f"Subscription updated with {len(new_configs)} new configs.")

# --- STATS MANAGER ---
class StatsManager:
    def __init__(self):
        self.current_date = datetime.now(timezone.utc).strftime('%Y-%m-%d')
        self.data = self.load_data()

    def load_data(self):
        if os.path.exists(STATS_FILE):
            try:
                with open(STATS_FILE, 'r') as f:
                    return json.load(f)
            except: pass
        return {
            'date': self.current_date,
            'configs': 0,
            'proxies': 0,
            'files': 0
        }

    def save_data(self):
        with open(STATS_FILE, 'w') as f:
            json.dump(self.data, f)

    async def check_date_and_report(self, client, chat_id):
        """
        Checks if the date changed. 
        Returns True if it's a new day (to trigger resets), False otherwise.
        """
        stored_date = self.data.get('date')
        
        if stored_date != self.current_date:
            # 1. Send Report
            jalali_date = JalaliConverter.get_jalali_date_from_str(stored_date)
            total = self.data['configs'] + self.data['proxies'] + self.data['files']
            
            report_msg = (
                f"📊 **گزارش عملکرد ربات**\n"
                f"📅 تاریخ: {jalali_date}\n\n"
                f"⚙️ کانفیگ‌های پست شده: {self.data['configs']}\n"
                f"🛡 پروکسی‌های پست شده: {self.data['proxies']}\n"
                f"📂 فایل‌های پست شده: {self.data['files']}\n\n"
                f"✅ **مجموع کل:** {total}"
            )

            try:
                if total > 0:
                    await client.send_message(chat_id, report_msg)
                    logger.info("Daily report sent.")
            except Exception as e:
                logger.error(f"Failed to send daily report: {e}")

            # 2. Reset Data
            self.data = {
                'date': self.current_date,
                'configs': 0,
                'proxies': 0,
                'files': 0
            }
            self.save_data()
            return True # New Day Detected
            
        return False # Same Day

    def increment(self, category):
        # Safety check for date change mid-execution
        if self.data.get('date') != self.current_date:
            self.data['date'] = self.current_date
            self.data['configs'] = 0
            self.data['proxies'] = 0
            self.data['files'] = 0
            
        if category in self.data:
            self.data[category] += 1
            self.save_data()

# --- CLOUDFLARE ---
class CloudflareManager:
    def __init__(self):
        self.networks = []
        for cidr in ["2400:cb00::/32", "2606:4700::/32", "2803:f800::/32", "2405:b500::/32", "2405:8100::/32", "2a06:98c0::/29", "2c0f:f248::/32"]:
            try: self.networks.append(ipaddress.ip_network(cidr))
            except: pass

    async def update_ranges(self):
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(CF_RANGES_URL, timeout=10) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        for line in text.splitlines():
                            line = line.strip()
                            if line and not line.startswith('#'):
                                try: self.networks.append(ipaddress.ip_network(line))
                                except: pass
        except: pass

    def is_cloudflare(self, ip_str):
        if not ip_str: return False
        try:
            clean = ip_str.strip('[]')
            obj = ipaddress.ip_address(clean)
            for net in self.networks:
                if obj in net: return True
        except: pass
        return False

# --- CONFIG MANAGER ---
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
                for k in ['ps', 'remarks', 'id']: data.pop(k, None)
            
            elif proto in ['vless', 'trojan', 'tuic', 'hysteria', 'ss', 'hysteria2']:
                parsed = urlparse(content)
                host_port = parsed.netloc.split('@')[-1]
                params = parse_qs(parsed.query)
                flat_params = {k: v[0] for k, v in params.items()}
                for key in ['fp', 'pbk', 'sid', 'spx']: flat_params.pop(key, None)
                data = {'protocol': proto, 'host_port': host_port, 'path': parsed.path, 'params': flat_params}

            elif proto == 'mtproto':
                parsed = urlparse(content.replace('tg://', 'http://'))
                params = parse_qs(parsed.query)
                data = {
                    'protocol': 'mtproto',
                    'server': params.get('server', [''])[0],
                    'port': params.get('port', [''])[0],
                    'secret': params.get('secret', [''])[0]
                }
            if not data: return content
            return json.dumps(data, sort_keys=True)
        except: return content

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
                with open(HISTORY_FILE, 'r') as f: self.history = json.load(f)
            except: self.history = {}
        curr = datetime.now(timezone.utc).timestamp()
        cutoff = curr - (DEDUPE_HOURS * 3600)
        self.history = {k: v for k, v in self.history.items() if v > cutoff}

    def save_history(self):
        with open(HISTORY_FILE, 'w') as f: json.dump(self.history, f)

    def is_duplicate(self, unique_str):
        fp = hashlib.sha256(unique_str.encode('utf-8')).hexdigest()
        if fp in self.history: return True
        self.history[fp] = datetime.now(timezone.utc).timestamp()
        return False

    async def setup_external_resources(self):
        if not os.path.exists(GEOIP_DB) or (datetime.now().timestamp() - os.path.getmtime(GEOIP_DB) > 86400):
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
        except: pass
        if host in self.dns_cache: return self.dns_cache[host]
        try:
            loop = asyncio.get_running_loop()
            ip = await loop.run_in_executor(None, socket.gethostbyname, host)
            self.dns_cache[host] = ip
            return ip
        except: return None

    def get_location_info(self, ip_str):
        if self.cf_manager.is_cloudflare(ip_str): return "☁️", "کلودفلر"
        if not self.geo_reader or not ip_str: return "🏁", "نامشخص"
        try:
            resp = self.geo_reader.country(ip_str)
            iso = resp.country.iso_code
            name = resp.country.names.get('en', 'Unknown')
            persian_names = {'Germany': 'آلمان', 'United States': 'آمریکا', 'Netherlands': 'هلند', 'France': 'فرانسه', 'United Kingdom': 'انگلیس', 'Finland': 'فنلاند', 'Canada': 'کانادا', 'Turkey': 'ترکیه', 'Russia': 'روسیه', 'Singapore': 'سنگاپور', 'Japan': 'ژاپن', 'Sweden': 'سوئد', 'United Arab Emirates': 'امارات', 'Switzerland': 'سوئیس'}
            return (chr(127397 + ord(iso[0])) + chr(127397 + ord(iso[1])) if iso else "🏁"), persian_names.get(name, name)
        except: return "🏁", "نامشخص"

    @staticmethod
    def parse_config_details(config_str, proto):
        try:
            if proto == 'vmess':
                b64 = config_str[8:]
                padding = len(b64) % 4
                if padding: b64 += "=" * (4 - padding)
                data = json.loads(base64.b64decode(b64).decode('utf-8', errors='ignore'))
                return data.get('add'), data.get('port')
            elif proto == 'mtproto':
                parsed = urlparse(config_str.replace('tg://', 'http://'))
                params = parse_qs(parsed.query)
                return params.get('server', [None])[0], params.get('port', [None])[0]
            else:
                parsed = urlparse(config_str)
                return parsed.hostname, parsed.port
        except: return None, None

    @staticmethod
    async def check_connection(ip, port):
        if not ip or not port: return None
        try:
            start = time.perf_counter()
            conn = asyncio.open_connection(ip, int(port))
            reader, writer = await asyncio.wait_for(conn, timeout=TIMEOUT_TCP)
            end = time.perf_counter()
            writer.close()
            await writer.wait_closed()
            return int((end - start) * 1000)
        except: return None

    @staticmethod
    def calculate_file_hash(path):
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""): h.update(chunk)
        return h.hexdigest()

# --- MAIN ---
async def main():
    logger.info("Starting PSG Collector Bot...")
    
    manager = ConfigManager()
    stats = StatsManager()
    sub_manager = SubscriptionManager()
    
    await manager.setup_external_resources()
    
    user_client = TelegramClient(StringSession(SESSION_STRING), API_ID, API_HASH)
    bot_client = TelegramClient('bot_session', API_ID, API_HASH)
    
    await user_client.connect()
    await bot_client.start(bot_token=BOT_TOKEN)

    # 1. Date Check: Report & Trim Subscriptions (Keep last 50%)
    is_new_day = await stats.check_date_and_report(bot_client, DESTINATION_ID)
    if is_new_day:
        sub_manager.trim_files()

    try:
        with open(CHANNELS_FILE, 'r', encoding='utf-8') as f: sources = json.load(f)
    except: return

    # --- PHASE 1: COLLECT ---
    logger.info("Phase 1: Collecting...")
    collected_items = []
    
    # Calculate current time once for comparison
    current_time_ts = datetime.now(timezone.utc).timestamp()
    
    for source_username in sources.keys():
        try:
            logger.info(f"Scraping: {source_username}")
            try:
                entity = await user_client.get_entity(source_username)
            except ValueError: continue

            async for message in user_client.iter_messages(entity, limit=CHECK_LIMIT_PER_CHANNEL):
                if not message.date: continue
                ts = message.date.astimezone(timezone.utc).timestamp()
                
                # --- NEW RULE: If post is older than 72 hours, do not process ---
                # DEDUPE_HOURS is 72. 72 * 3600 converts it to seconds.
                if (current_time_ts - ts) > (DEDUPE_HOURS * 3600):
                    continue
                # -------------------------------------------------------------
                
                if message.file and message.file.name and message.file.name.lower().endswith(NPV_EXTENSIONS):
                    collected_items.append({'ts': ts, 'type': 'file', 'msg_obj': message, 'source': source_username})
                    continue

                if message.text:
                    for match in re.finditer(VMESS_REGEX, message.text, re.IGNORECASE):
                        collected_items.append({'ts': ts, 'type': 'text', 'proto': match.group(1), 'raw': match.group(0), 'source': source_username})
                    for match in re.finditer(MTPROTO_REGEX, message.text, re.IGNORECASE):
                        collected_items.append({'ts': ts, 'type': 'text', 'proto': 'mtproto', 'raw': match.group(0), 'source': source_username})

            await asyncio.sleep(FETCH_DELAY)
        except Exception as e:
            logger.warning(f"Error scraping {source_username}: {e}")
            await asyncio.sleep(FETCH_DELAY)

    # --- PHASE 2: PROCESS & SUBSCRIBE ---
    collected_items.sort(key=lambda x: x['ts'])
    logger.info(f"Phase 2: Processing {len(collected_items)} items...")
    
    valid_subscription_configs = []

    for item in collected_items:
        try:
            shamsi_date = JalaliConverter.get_persian_time(item['ts'])
            
            if item['type'] == 'text':
                # Remove trailing backticks or quotes if captured
                config_str = item['raw'].strip('`"\'')
                proto = item['proto']
                
                norm_json = ConfigNormalizer.normalize(config_str, proto)
                if not norm_json or manager.is_duplicate(norm_json): continue

                host, port = manager.parse_config_details(config_str, proto)
                if not host: continue
                ip = await manager.resolve_dns(host)
                if not ip: continue
                
                ping_ms = await manager.check_connection(ip, port)
                if ping_ms is None: continue

                # Collect for subscription (exclude mtproto)
                if proto != 'mtproto':
                    valid_subscription_configs.append(config_str)

                flag, country = manager.get_location_info(ip)
                clean_proto = proto.upper().replace('VMESS', 'VMess').replace('VLESS', 'VLESS')
                
                # Generate Tags
                tags = f"#{clean_proto} #VPN"
                if proto == 'mtproto':
                    tags = "#Proxy #MTProto"
                elif proto == 'ss':
                    tags = "#Shadowsocks #VPN"

                caption = (
                    f"📂 کانفیگ {clean_proto}\n"
                    f"📍 لوکیشن: {country} {flag}\n"
                    f"📶 پینگ: {ping_ms}ms\n\n"
                    f"{tags}\n\n"
                    f"🕒 انتشار: {shamsi_date}\n"
                    f"💡 منبع: @{item['source']}\n"
                )
                
                buttons = []
                if proto == 'mtproto': 
                    buttons.append([Button.url("⚡️ اتصال (Connect)", config_str)])
                buttons.append([Button.url("🔍 دریافت کانفیگ‌های بیشتر", CHANNEL_LINK)])

                await bot_client.send_message(DESTINATION_ID, f"{caption}\n```{config_str}```\n", buttons=buttons, link_preview=False)
                
                if proto == 'mtproto':
                    stats.increment('proxies')
                else:
                    stats.increment('configs')
                
                await asyncio.sleep(4)

            elif item['type'] == 'file':
                msg = item['msg_obj']
                path = await msg.download_media(file=TEMP_DIR)
                if not path: continue

                file_hash = manager.calculate_file_hash(path)
                if manager.is_duplicate(file_hash):
                    os.remove(path); continue
                
                caption = (
                    f"📂 فایل کانفیگ NapsternetV\n"
                    f"📍 لوکیشن: نامشخص\n\n"
                    f"#NapsternetV #Config #File\n\n"
                    f"🕒 انتشار: {shamsi_date}\n"
                    f"💡 منبع: @{item['source']}\n\n"
                )
                
                await bot_client.send_file(DESTINATION_ID, path, caption=caption, buttons=[[Button.url("🔍 دریافت کانفیگ‌های بیشتر", CHANNEL_LINK)]])
                
                stats.increment('files')
                if os.path.exists(path): os.remove(path)
                await asyncio.sleep(4)

        except Exception as e:
            logger.error(f"Error processing item: {e}")

    # --- PHASE 3: UPDATE SUBSCRIPTION ---
    if valid_subscription_configs:
        sub_manager.update_subscription(valid_subscription_configs)

    if os.path.exists(TEMP_DIR): shutil.rmtree(TEMP_DIR)
    manager.save_history()
    await user_client.disconnect()
    await bot_client.disconnect()

if __name__ == '__main__':
    asyncio.run(main())
