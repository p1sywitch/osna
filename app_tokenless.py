# -*- coding: utf-8 -*-
"""
p1sy TOOLBOX
by:grego | p1sy
Kurulum: pip install -r requirements.txt
Çalıştır: python app.py
"""
import os, sys, json, base64, hashlib, hmac, socket, ssl, secrets
import urllib.parse, subprocess, re, random, string, ipaddress, time, smtplib, threading, html, uuid
import concurrent.futures, tempfile, shutil, sqlite3, unicodedata, statistics, math, csv, io, difflib
from datetime import datetime, timezone
from email.message import EmailMessage
from pathlib import Path
from functools import wraps

from flask import Flask, request, jsonify, Response, send_file, session, redirect, url_for, send_from_directory
from flask_limiter import Limiter
from flask_limiter.util import get_remote_address
from werkzeug.security import generate_password_hash, check_password_hash
from dotenv import load_dotenv

# .env dosyasini bu Python dosyasinin bulundugu klasorden yukle.
# Boylece CMD hangi klasorden acilirsa acilsin ayarlar okunur.
BASE_DIR = Path(__file__).resolve().parent
load_dotenv(BASE_DIR / ".env", override=False)

try:
    import requests
except ImportError:
    print("[HATA] pip install -r requirements.txt")
    sys.exit(1)

try:
    import dns.resolver
    HAS_DNS = True
except ImportError:
    HAS_DNS = False

try:
    import whois
    HAS_WHOIS = True
except ImportError:
    HAS_WHOIS = False

try:
    from bs4 import BeautifulSoup
    HAS_BS4 = True
except ImportError:
    HAS_BS4 = False


# ============================================================
# AYARLAR — SERVER-SIDE .env
# ============================================================
# Hem yeni OWNER_* isimleri hem de eski TOOLBOX_ADMIN_* isimleri desteklenir.
# Boylece mevcut .env dosyan varsa yeniden duzenlemen gerekmez.
ADMIN_USER = (os.getenv("OWNER_USERNAME") or os.getenv("TOOLBOX_ADMIN_USERNAME") or "").strip()
ADMIN_PASS = os.getenv("OWNER_PASSWORD") or os.getenv("TOOLBOX_ADMIN_PASSWORD") or ""
SECRET_KEY = os.getenv("TOOLBOX_SECRET_KEY") or ""
ENV_MODE = (os.getenv("ENV_MODE") or os.getenv("TOOLBOX_ENV") or "production").strip().lower()

# Discord bot/OAuth/rol entegrasyonu bu sürümde yoktur.
# Discord ID araçları yalnızca yerel hesaplama/format kontrolü yapar.


# Admin IP — istemiyorsan boş bırak
ALLOWED_IPS_RAW = ""
ADMIN_IPS_RAW = ""
ADMIN_IP_BYPASS = False

# ============================================================
# E-MAIL LOG — İSTEMİYORSAN BOŞ BIRAK
# ============================================================
SMTP_HOST = ""
SMTP_PORT = 587
SMTP_USER = ""
SMTP_PASSWORD = ""
LOG_EMAIL_TO = ""
LOG_EMAIL_ENABLED = False

ADMIN_IPS = {x.strip() for x in ADMIN_IPS_RAW.split(",") if x.strip()}

ALLOWED_IPS = set()
if ALLOWED_IPS_RAW:
    for ip in ALLOWED_IPS_RAW.split(","):
        ip = ip.strip()
        if ip:
            ALLOWED_IPS.add(ip)

errors = []
if not ADMIN_USER: errors.append("OWNER_USERNAME .env içinde ayarlanmalı")
if not ADMIN_PASS or len(ADMIN_PASS) < 12: errors.append("OWNER_PASSWORD en az 12 karakter olmalı")
if not SECRET_KEY or len(SECRET_KEY) < 32: errors.append("TOOLBOX_SECRET_KEY en az 32 karakter olmalı")

if errors:
    print("\n[GÜVENLİK HATASI]")
    for e in errors: print(f"  - {e}")
    print("\n.env dosyasını oluştur")
    sys.exit(1)


app = Flask(__name__)
app.config.update(
    SECRET_KEY=SECRET_KEY,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=(ENV_MODE == "production"),
    PERMANENT_SESSION_LIFETIME=3600,
    MAX_CONTENT_LENGTH=256 * 1024,
)

limiter = Limiter(get_remote_address, app=app,
                  default_limits=["300 per hour", "60 per minute"],
                  storage_uri="memory://")

ADMIN_HASH = generate_password_hash(ADMIN_PASS)
TEMP_DIR = Path(tempfile.gettempdir()) / "p1sy_files"
TEMP_DIR.mkdir(exist_ok=True)
BASE_DIR = Path(__file__).resolve().parent
STATIC_DIR = BASE_DIR / "static"
STATIC_DIR.mkdir(exist_ok=True)
LOG_FILE = BASE_DIR / "logs.txt"
LOG_FILE.touch(exist_ok=True)
DB_FILE = BASE_DIR / "users.db"

def db_conn():
    c = sqlite3.connect(DB_FILE)
    c.row_factory = sqlite3.Row
    return c

def init_db():
    with db_conn() as c:
        c.execute("""CREATE TABLE IF NOT EXISTS users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL,
            role TEXT NOT NULL DEFAULT 'user',
            discord_id TEXT
        )""")
        cols = {row["name"] for row in c.execute("PRAGMA table_info(users)").fetchall()}
        if "role" not in cols:
            c.execute("ALTER TABLE users ADD COLUMN role TEXT NOT NULL DEFAULT 'user'")
        if "discord_id" not in cols:
            c.execute("ALTER TABLE users ADD COLUMN discord_id TEXT")
        c.commit()
init_db()

TIMEOUT = 10
HEADERS = {"User-Agent": "Mozilla/5.0 (compatible; p1syWeb/2.0)"}

BLOCKED_NETS = [
    ipaddress.ip_network("10.0.0.0/8"), ipaddress.ip_network("172.16.0.0/12"),
    ipaddress.ip_network("192.168.0.0/16"), ipaddress.ip_network("127.0.0.0/8"),
    ipaddress.ip_network("169.254.0.0/16"), ipaddress.ip_network("0.0.0.0/8"),
    ipaddress.ip_network("100.64.0.0/10"), ipaddress.ip_network("::1/128"),
    ipaddress.ip_network("fc00::/7"), ipaddress.ip_network("fe80::/10"),
]


def is_ip_safe(ip_str):
    try:
        ip = ipaddress.ip_address(ip_str)
        for net in BLOCKED_NETS:
            if ip in net: return False
        return True
    except Exception:
        return False


def resolve_host_safe(host):
    try:
        ips = socket.getaddrinfo(host, None)
        for ip in set(x[4][0] for x in ips):
            if not is_ip_safe(ip):
                return False, f"Yasaklı IP: {ip}"
        return True, None
    except Exception as e:
        return False, f"DNS hatası: {e}"


def validate_url(url, allow_http=False):
    if not url or not isinstance(url, str): return False, "URL gerekli"
    if len(url) > 2000: return False, "URL çok uzun"
    try: p = urllib.parse.urlparse(url)
    except Exception: return False, "URL parse edilemedi"
    if p.scheme not in ("http", "https"): return False, "Sadece http/https"
    if not p.hostname: return False, "Hostname yok"
    ok, msg = resolve_host_safe(p.hostname)
    if not ok: return False, msg
    return True, None


def safe_get(url, allow_http=False, **kwargs):
    ok, msg = validate_url(url, allow_http=allow_http)
    if not ok: raise ValueError(msg)
    kwargs.setdefault("headers", HEADERS)
    kwargs.setdefault("timeout", TIMEOUT)
    kwargs.setdefault("allow_redirects", False)
    r = requests.get(url, **kwargs)
    if r.is_redirect:
        loc = r.headers.get("Location", "")
        if loc:
            loc = urllib.parse.urljoin(url, loc)
            ok2, msg2 = validate_url(loc, allow_http=allow_http)
            if not ok2: raise ValueError(f"Yasaklı redirect: {msg2}")
    return r


def _send_log_email(event, extra):
    if not (LOG_EMAIL_ENABLED and SMTP_HOST and SMTP_USER and SMTP_PASSWORD and LOG_EMAIL_TO):
        return
    # Never send secrets or client IPs to e-mail.
    safe = str(extra or "")
    for secret in (SMTP_PASSWORD, ADMIN_PASS):
        if secret:
            safe = safe.replace(secret, "[REDACTED]")
    safe = safe.replace(request.remote_addr or "", "[IP-HIDDEN]") if request else safe
    msg = EmailMessage()
    msg["Subject"] = f"[p1sy TOOLBOX] {event}"
    msg["From"] = SMTP_USER
    msg["To"] = LOG_EMAIL_TO
    msg.set_content(f"Zaman: {datetime.now().isoformat(timespec='seconds')}\nOlay: {event}\nDetay: {safe[:2000]}")
    try:
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT, timeout=10) as s:
            s.starttls()
            s.login(SMTP_USER, SMTP_PASSWORD)
            s.send_message(msg)
    except Exception:
        pass

def log_event(event, extra=""):
    # Gizlilik: istemci IP adresi kalıcı olarak kaydedilmez veya e-postalanmaz.
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    safe_extra = str(extra or "")[:420]
    try:
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"[{ts}] [{event}] {safe_extra}\n")
    except Exception:
        pass
    if LOG_EMAIL_ENABLED:
        threading.Thread(target=_send_log_email, args=(event, safe_extra), daemon=True).start()


def ok(data, msg="Başarılı"):
    return jsonify({"status": "ok", "message": msg, "data": data})


def err(msg, code=200):
    return jsonify({"status": "error", "message": str(msg)[:300]}), code


def login_required(f):
    @wraps(f)
    def w(*a, **kw):
        if not session.get("logged_in"): return err("Giriş gerekli", 401)
        return f(*a, **kw)
    return w

def _current_user_is_admin():
    if session.get("role") == "admin":
        return True
    if session.get("username") == ADMIN_USER and ADMIN_USER:
        return True
    return False


def admin_required(f):
    @wraps(f)
    def w(*a, **kw):
        if not session.get("logged_in"):
            return err("Giriş gerekli", 401)
        if not _current_user_is_admin():
            return err("Admin yetkisi gerekli", 403)
        return f(*a, **kw)
    return w

def admin_required(f):
    @wraps(f)
    def w(*a, **kw):
        if not session.get("logged_in"):
            return err("Giriş gerekli", 401)
        if not _current_user_is_admin():
            return err("Admin yetkisi gerekli", 403)
        return f(*a, **kw)
    return w


@app.before_request
def ip_guard():
    # IP adresi kalıcı olarak kaydedilmez. ALLOWED_IPS verilirse ek erişim kısıtı uygulanır.
    if request.path.startswith("/static/"): return None
    if ALLOWED_IPS and (request.remote_addr or "") not in ALLOWED_IPS:
        return err("Erişim yok", 403)
    return None


@app.after_request
def sec_headers(resp):
    if request.path.startswith("/static/"): return resp
    resp.headers["X-Content-Type-Options"] = "nosniff"
    resp.headers["X-Frame-Options"] = "DENY"
    resp.headers["Referrer-Policy"] = "no-referrer"
    resp.headers["Permissions-Policy"] = "geolocation=(), microphone=(), camera=()"
    resp.headers["Content-Security-Policy"] = (
        "default-src 'self'; script-src 'self' 'unsafe-inline'; "
        "style-src 'self' 'unsafe-inline'; img-src 'self' data: https:; "
        "media-src 'self'; connect-src 'self'; frame-ancestors 'none'"
    )
    return resp


@app.route("/static/<path:filename>")
def static_files(filename):
    try:
        safe = os.path.basename(filename)
        return send_from_directory(str(STATIC_DIR), safe)
    except Exception:
        return "Bulunamadı", 404


HTML_LOGIN = r"""<!DOCTYPE html><html lang="tr"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>p1sy - Giriş</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#08080d;--card:#12121d;--border:#232336;--text:#eaeaf5;--dim:#6d6d8a;--purple:#a855f7;--pink:#ec4899;--red:#ef4444;--green:#22c55e}
body{font-family:-apple-system,'Segoe UI',Roboto,sans-serif;background:var(--bg);color:var(--text);min-height:100vh;display:flex;align-items:center;justify-content:center;overflow:hidden}
body::before{content:'';position:fixed;inset:0;z-index:-2;background-image:linear-gradient(rgba(168,85,247,.06) 1px,transparent 1px),linear-gradient(90deg,rgba(168,85,247,.06) 1px,transparent 1px);background-size:44px 44px}
body::after{content:'';position:fixed;top:-300px;left:50%;transform:translateX(-50%);width:800px;height:800px;z-index:-1;background:radial-gradient(circle,rgba(168,85,247,.22) 0%,transparent 65%);filter:blur(90px)}
.box{background:var(--card);border:1px solid var(--border);border-radius:20px;padding:40px 36px;width:100%;max-width:400px;box-shadow:0 24px 80px rgba(0,0,0,.6);position:relative;z-index:10}
.logo-rgb{text-align:center;font-size:42px;font-weight:900;letter-spacing:-1.5px;background:linear-gradient(90deg,#ff0080,#ff8c00,#ffd700,#00ff88,#00d4ff,#a855f7,#ff0080);background-size:300% 100%;-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;animation:rgb 5s linear infinite}
@keyframes rgb{0%{background-position:0% 50%}100%{background-position:300% 50%}}
.tag{text-align:center;font-size:11px;color:var(--dim);letter-spacing:2px;font-weight:700;margin:8px 0 28px}
.tag span{background:linear-gradient(90deg,var(--purple),var(--pink));-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;font-weight:900}
.field{display:flex;flex-direction:column;gap:6px;margin-bottom:16px}
.field label{font-size:10px;font-weight:800;letter-spacing:1.5px;color:var(--dim);text-transform:uppercase}
.field input{background:var(--bg);border:1px solid var(--border);color:var(--text);padding:13px 16px;border-radius:10px;font-family:'Courier New',monospace;font-size:14px;outline:none;width:100%}
.field input:focus{border-color:var(--purple)}
.btn{width:100%;border:none;padding:14px;border-radius:10px;font-family:inherit;font-size:14px;font-weight:800;cursor:pointer;background:linear-gradient(135deg,var(--purple),var(--pink));color:#fff}
.btn:disabled{opacity:.6;cursor:not-allowed}
.msg{text-align:center;font-size:12px;font-weight:700;padding:10px;border-radius:8px;margin-top:14px;display:none}
.msg.show{display:block}
.msg.bad{background:rgba(239,68,68,.15);color:var(--red)}
.msg.ok{background:rgba(34,197,94,.15);color:var(--green)}
.music-btn{position:fixed;bottom:20px;right:20px;background:var(--purple);color:#fff;border:none;padding:12px 20px;border-radius:10px;font-weight:800;cursor:pointer;font-family:inherit;font-size:12px;z-index:999;box-shadow:0 8px 30px rgba(168,85,247,.5)}
.music-btn:hover{transform:translateY(-2px)}
</style></head><body>
<audio id="bgMusic" src="/static/baba.mp3" loop preload="auto"></audio>
<button class="music-btn" id="musicBtn" onclick="toggleMusic()">🔊 Müziği Çal</button>

<div class="box">
<div class="logo-rgb">p1sy</div>
<div class="tag">BY <span>grego</span> | <span>p1sy</span></div>
<div class="field"><label>Kullanıcı Adı</label><input id="u" placeholder="kullanici_adi" autocomplete="username"></div>
<div class="field"><label>Şifre</label><input type="password" id="p" placeholder="••••••••" autocomplete="current-password"></div>
<button class="btn" id="btn" onclick="doLogin()">GİRİŞ YAP</button>
<button class="btn" style="margin-top:10px;background:transparent;border:1px solid var(--border)" onclick="doRegister()">KAYIT OL</button>
<div class="msg" id="msg"></div>
</div>
<script>
function toggleMusic(){
  const m=document.getElementById("bgMusic");
  const b=document.getElementById("musicBtn");
  if(m.paused){m.play().then(()=>{b.textContent="⏸ Müziği Durdur";}).catch(e=>console.log("müzik:",e));}
  else{m.pause();b.textContent="🔊 Müziği Çal";}
}
document.addEventListener("click",function once(){
  const m=document.getElementById("bgMusic");
  if(m && m.paused){
    m.play().then(()=>{document.getElementById("musicBtn").textContent="⏸ Müziği Durdur";}).catch(()=>{});
  }
  document.removeEventListener("click",once);
});
async function doLogin(){
  const u=document.getElementById("u").value.trim();
  const p=document.getElementById("p").value;
  const btn=document.getElementById("btn"), msg=document.getElementById("msg");
  if(!u||!p){msg.textContent="Boş bırakma";msg.className="msg show bad";return;}
  btn.disabled=true;btn.textContent="GİRİLİYOR...";
  try{
    const r=await fetch("/api/login",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({username:u,password:p})});
    const d=await r.json();
    if(d.status==="ok"){msg.textContent="Başarılı";msg.className="msg show ok";setTimeout(()=>location.href="/app",500);}
    else{msg.textContent=d.message||"Hatalı";msg.className="msg show bad";}
  }catch(e){msg.textContent="Bağlantı hatası";msg.className="msg show bad";}
  finally{btn.disabled=false;btn.textContent="GİRİŞ YAP";}
}
async function doRegister(){
  const u=document.getElementById("u").value.trim();
  const p=document.getElementById("p").value;
  const msg=document.getElementById("msg");
  if(!/^[a-zA-Z0-9_.-]{3,32}$/.test(u)){msg.textContent="Kullanıcı adı 3-32 karakter olmalı";msg.className="msg show bad";return;}
  if(p.length<8){msg.textContent="Şifre en az 8 karakter olmalı";msg.className="msg show bad";return;}
  try{
    const r=await fetch("/api/register",{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify({username:u,password:p})});
    const d=await r.json();
    msg.textContent=d.message||"Tamam";msg.className="msg show "+(d.status==="ok"?"ok":"bad");
  }catch(e){msg.textContent="Bağlantı hatası";msg.className="msg show bad";}
}

document.addEventListener("keydown",e=>{if(e.key==="Enter")doLogin();});
</script></body></html>
"""


HTML_APP = r"""<!DOCTYPE html><html lang="tr"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>p1sy</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#08080d;--bg2:#0d0d16;--card:#12121d;--card2:#181826;--border:#232336;--border2:#2e2e45;--text:#eaeaf5;--dim:#6d6d8a;--dim2:#4a4a5e;--purple:#a855f7;--indigo:#6366f1;--pink:#ec4899;--green:#22c55e;--red:#ef4444;--yellow:#eab308;--cyan:#06b6d4;--orange:#f97316}
body{font-family:-apple-system,'Segoe UI',Roboto,sans-serif;background:var(--bg);color:var(--text);min-height:100vh}
body::before{content:'';position:fixed;inset:0;z-index:-2;background-image:linear-gradient(rgba(168,85,247,.05) 1px,transparent 1px),linear-gradient(90deg,rgba(168,85,247,.05) 1px,transparent 1px);background-size:44px 44px}
body::after{content:'';position:fixed;top:-350px;left:50%;transform:translateX(-50%);width:900px;height:900px;z-index:-1;background:radial-gradient(circle,rgba(168,85,247,.2) 0%,transparent 65%);filter:blur(90px)}
.header{display:flex;align-items:center;justify-content:space-between;padding:18px 32px;border-bottom:1px solid var(--border);background:rgba(8,8,13,.8);backdrop-filter:blur(24px);position:sticky;top:0;z-index:100}
.logo{display:flex;align-items:center;gap:16px}
.logo-rgb{font-size:34px;font-weight:900;letter-spacing:-1.5px;background:linear-gradient(90deg,#ff0080,#ff8c00,#ffd700,#00ff88,#00d4ff,#a855f7,#ff0080);background-size:300% 100%;-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;animation:rgb 5s linear infinite}
@keyframes rgb{0%{background-position:0% 50%}100%{background-position:300% 50%}}
.logo-meta{display:flex;flex-direction:column;gap:3px;padding-left:16px;border-left:1px solid var(--border)}
.logo-by{font-size:11px;color:var(--dim);font-weight:700;letter-spacing:1.5px}
.logo-by span{background:linear-gradient(90deg,var(--purple),var(--pink));-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;font-weight:900}
.user-badge{font-size:11px;font-weight:700;color:var(--purple);padding:8px 14px;background:var(--card);border:1px solid var(--border);border-radius:10px}
.logout{background:transparent;border:1px solid var(--border);color:var(--dim);padding:8px 14px;border-radius:10px;cursor:pointer;font-family:inherit;font-size:11px;font-weight:700}
.logout:hover{color:var(--red);border-color:var(--red)}
.header-right{display:flex;align-items:center;gap:10px}
.wrap{display:grid;grid-template-columns:220px 1fr;gap:22px;padding:22px 32px;max-width:1600px;margin:0 auto}
.sidebar{background:var(--card);border:1px solid var(--border);border-radius:16px;padding:20px;position:sticky;top:100px;height:fit-content;max-height:calc(100vh - 120px);overflow-y:auto}
.sidebar-label{font-size:10px;font-weight:800;letter-spacing:2.5px;color:var(--dim2);margin-bottom:14px}
#nav{display:flex;flex-direction:column;gap:3px}
.nav-btn{background:transparent;border:none;color:var(--text);text-align:left;padding:9px 12px;border-radius:9px;cursor:pointer;font-family:inherit;font-size:12px;font-weight:600;display:flex;align-items:center;justify-content:space-between;transition:all .15s}
.nav-btn:hover{background:var(--card2)}
.nav-btn.active{background:linear-gradient(135deg,rgba(168,85,247,.22),rgba(99,102,241,.15));color:#fff}
.nav-count{font-size:9px;opacity:.6;font-family:'Courier New',monospace;background:var(--bg2);padding:2px 6px;border-radius:5px}
.content{display:flex;flex-direction:column;gap:18px;min-width:0}
.search input{width:100%;background:var(--card);border:1px solid var(--border);color:var(--text);padding:14px 18px;border-radius:12px;font-family:inherit;font-size:14px;outline:none}
.search input:focus{border-color:var(--purple)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:10px}
.tool{background:var(--card);border:1px solid var(--border);border-radius:11px;padding:14px;cursor:pointer;transition:all .2s;animation:ci .3s ease backwards}
@keyframes ci{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:translateY(0)}}
.tool:hover{border-color:var(--purple);transform:translateY(-2px);box-shadow:0 8px 25px rgba(168,85,247,.2)}
.tool-num{font-family:'Courier New',monospace;font-size:10px;color:var(--purple);font-weight:900}
.tool-name{font-size:13px;font-weight:700;margin:6px 0 4px;line-height:1.3}
.tool-cat{font-size:9px;color:var(--dim);text-transform:uppercase;letter-spacing:1px;font-weight:700}
.modal{position:fixed;inset:0;background:rgba(5,5,10,.88);backdrop-filter:blur(10px);display:flex;align-items:center;justify-content:center;z-index:500}
.modal.hide{display:none}
.modal-box{background:var(--card);border:1px solid var(--border2);border-radius:18px;width:92%;max-width:520px;overflow:hidden;box-shadow:0 24px 80px rgba(0,0,0,.6)}
.modal-head{display:flex;align-items:center;justify-content:space-between;padding:18px 22px;border-bottom:1px solid var(--border);background:linear-gradient(180deg,var(--card2),var(--card))}
.modal-head h3{font-size:15px;font-weight:900;background:linear-gradient(90deg,var(--purple),var(--pink));-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent}
.close{background:transparent;border:none;color:var(--dim);font-size:18px;cursor:pointer;width:30px;height:30px;border-radius:8px}
.close:hover{background:var(--card2);color:var(--red)}
.modal-body{padding:22px;display:flex;flex-direction:column;gap:14px;max-height:60vh;overflow-y:auto}
.field{display:flex;flex-direction:column;gap:6px}
.field label{font-size:10px;font-weight:800;letter-spacing:1.5px;color:var(--dim);text-transform:uppercase}
.field input,.field textarea{background:var(--bg2);border:1px solid var(--border);color:var(--text);padding:12px 15px;border-radius:10px;font-family:'Courier New',monospace;font-size:13px;outline:none;width:100%}
.field textarea{resize:vertical;min-height:100px}
.field input:focus,.field textarea:focus{border-color:var(--purple)}
.modal-foot{padding:16px 22px;border-top:1px solid var(--border);display:flex;justify-content:flex-end;gap:10px;background:var(--bg2)}
.btn{padding:11px 24px;border-radius:10px;font-family:inherit;font-size:13px;font-weight:800;cursor:pointer;border:none}
.btn-primary{background:linear-gradient(135deg,var(--purple),var(--pink));color:#fff}
.btn-primary:disabled{opacity:.6;cursor:not-allowed}
.btn-ghost{background:transparent;color:var(--dim);border:1px solid var(--border)}
.result{background:var(--card);border:1px solid var(--border);border-radius:16px;overflow:hidden;animation:su .3s ease}
@keyframes su{from{opacity:0;transform:translateY(15px)}to{opacity:1;transform:translateY(0)}}
.result.hide{display:none}
.result-head{display:flex;align-items:center;justify-content:space-between;padding:14px 22px;background:var(--bg2);border-bottom:1px solid var(--border)}
.result-title{font-weight:800;font-size:14px}
.result-actions{display:flex;gap:6px}
.icon-btn{background:transparent;border:1px solid var(--border);color:var(--dim);width:32px;height:32px;border-radius:9px;cursor:pointer;font-size:13px}
.icon-btn:hover{color:var(--purple);border-color:var(--purple)}
.result-body{padding:18px 22px;font-family:'Courier New',monospace;font-size:12px;line-height:1.7;max-height:700px;overflow-y:auto;white-space:pre-wrap;word-break:break-all}
.k{color:var(--cyan);font-weight:700}
.v{color:var(--text)}
.line{padding:3px 0;border-bottom:1px solid rgba(255,255,255,.03)}
.ok{color:var(--green)}
.bad{color:var(--red)}
.warn{color:var(--yellow)}
.info{color:var(--cyan)}
.empty{color:var(--dim);padding:20px;text-align:center}
.code-box{background:var(--bg);border:1px solid var(--border);border-radius:8px;padding:12px;font-size:11px;max-height:400px;overflow:auto;color:var(--cyan);white-space:pre}
.dl{background:linear-gradient(135deg,var(--green),var(--cyan));color:#fff;padding:9px 16px;border-radius:8px;text-decoration:none;font-weight:800;font-size:11px;display:inline-block;margin-top:8px}
.profile-box{display:flex;gap:16px;align-items:flex-start;flex-wrap:wrap;margin:10px 0;padding:16px;background:var(--bg2);border:1px solid var(--border);border-radius:12px}
.profile-avatar{width:128px;height:128px;border-radius:50%;border:3px solid var(--purple);object-fit:cover;box-shadow:0 8px 30px rgba(168,85,247,.4)}
.profile-banner{border-radius:12px;border:2px solid var(--purple);overflow:hidden;background:var(--bg2)}
.profile-banner img{width:100%;max-width:400px;height:auto;display:block;min-height:128px;object-fit:cover}
.hesap-box{background:linear-gradient(135deg,rgba(168,85,247,.08),rgba(236,72,153,.08));border:1px solid var(--purple);border-radius:12px;padding:16px;margin:12px 0}
.hesap-title{font-size:12px;font-weight:900;color:var(--purple);letter-spacing:1.5px;margin-bottom:10px;text-transform:uppercase}
.hesap-row{padding:4px 0;border-bottom:1px solid rgba(255,255,255,.04);display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap}
.hesap-key{color:var(--cyan);font-weight:700}
.hesap-val{color:var(--text);text-align:right}
.hesap-note{margin-top:10px;padding:8px;background:rgba(234,179,8,.1);border:1px solid var(--yellow);border-radius:8px;font-size:10px;color:var(--yellow);text-align:center}
.toast{position:fixed;bottom:28px;right:28px;background:var(--card);border:1px solid var(--border2);border-left:3px solid var(--purple);color:var(--text);padding:14px 22px;border-radius:12px;font-size:13px;font-weight:700;transform:translateX(450px);transition:transform .3s;z-index:1000;max-width:340px}
.toast.show{transform:translateX(0)}
.toast.success{border-left-color:var(--green)}
.toast.error{border-left-color:var(--red)}
.spin{display:inline-block;width:14px;height:14px;border:2px solid rgba(255,255,255,.25);border-top-color:#fff;border-radius:50%;animation:sp .7s linear infinite;vertical-align:middle}
@keyframes sp{to{transform:rotate(360deg)}}
.foot{text-align:center;padding:22px;font-size:11px;color:var(--dim2);letter-spacing:1.5px;font-weight:700;border-top:1px solid var(--border);margin-top:40px}
.foot span{background:linear-gradient(90deg,var(--purple),var(--pink));-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;font-weight:900}
.music-btn{position:fixed;bottom:20px;right:20px;background:var(--purple);color:#fff;border:none;padding:12px 20px;border-radius:10px;font-weight:800;cursor:pointer;font-family:inherit;font-size:12px;z-index:999;box-shadow:0 8px 30px rgba(168,85,247,.5)}
.music-btn:hover{transform:translateY(-2px)}
</style></head><body>

<audio id="bgMusic" src="/static/baba.mp3" loop preload="auto"></audio>
<button class="music-btn" id="musicBtn" onclick="toggleMusic()">🔊 Müziği Çal</button>

<header class="header">
  <div class="logo">
    <div class="logo-rgb">p1sy</div>
    <div class="logo-meta">
      <div class="logo-by">BY <span>grego</span> | <span>p1sy</span></div>
    </div>
  </div>
  <div class="header-right">
    <div class="user-badge">👤 <span id="me">-</span></div>
    <button class="logout" id="adminBadge" style="display:none" onclick="setCatAdmin()">🛡 ADMIN</button>
    <button class="logout" onclick="logout()">ÇIKIŞ</button>
  </div>
</header>

<div class="wrap">
  <aside class="sidebar">
    <div class="sidebar-label">KATEGORİLER</div>
    <div id="nav"></div>
  </aside>
  <main class="content">
    <div class="search"><input id="search" placeholder="Araç ara..."></div>
    <div id="grid" class="grid"></div>
    <div id="result" class="result hide">
      <div class="result-head">
        <div class="result-title" id="rTitle">Sonuç</div>
        <div class="result-actions">
          <button class="icon-btn" id="copyBtn">📋</button>
          <button class="icon-btn" id="closeBtn">✕</button>
        </div>
      </div>
      <div class="result-body" id="rBody"></div>
    </div>
  </main>
</div>

<div class="foot">p1sy • BY <span>grego</span> | <span>p1sy</span></div>

<div id="modal" class="modal hide">
  <div class="modal-box">
    <div class="modal-head"><h3 id="mTitle">Araç</h3><button class="close" onclick="closeM()">✕</button></div>
    <div class="modal-body" id="mBody"></div>
    <div class="modal-foot">
      <button class="btn btn-ghost" onclick="closeM()">İPTAL</button>
      <button class="btn btn-primary" id="runBtn">ÇALIŞTIR</button>
    </div>
  </div>
</div>

<div id="toast" class="toast"></div>

<script>
const TOOLS = [
{n:1,name:"IP Sorgula",cat:"OSINT",api:"/api/ip",in:[{k:"ip",l:"IP Adresi",p:"8.8.8.8"}]},
{n:2,name:"CIDR Hesapla",cat:"OSINT",api:"/api/cidr",in:[{k:"cidr",l:"CIDR",p:"192.168.1.0/24"}]},
{n:3,name:"MAC Sorgu",cat:"OSINT",api:"/api/mac",in:[{k:"mac",l:"MAC",p:"00:1A:2B"}]},
{n:4,name:"Email/Username OSINT",cat:"OSINT",api:"/api/email",in:[{k:"q",l:"Email/Username",p:"ornek@mail.com"}]},
{n:5,name:"Telefon Numara",cat:"OSINT",api:"/api/phone",in:[{k:"num",l:"Numara",p:"+905551234567"}]},
{n:6,name:"Username Checker (~60 site)",cat:"OSINT",api:"/api/usercheck",in:[{k:"username",l:"Kullanıcı adı",p:"grego"}]},
{n:7,name:"MyIP + Konum",cat:"OSINT",api:"/api/myip",in:[]},
{n:8,name:"DNS Kayıtları",cat:"NET",api:"/api/dns",in:[{k:"domain",l:"Domain",p:"example.com"}]},
{n:9,name:"Reverse DNS",cat:"NET",api:"/api/rdns",in:[{k:"ip",l:"IP",p:"8.8.8.8"}]},
{n:10,name:"Traceroute",cat:"NET",api:"/api/trace",in:[{k:"host",l:"Host",p:"google.com"}]},
{n:11,name:"Port Tarayıcı",cat:"NET",api:"/api/portscan",in:[{k:"host",l:"Host",p:"scanme.nmap.org"},{k:"range",l:"Port Aralığı",p:"80-100"}]},
{n:12,name:"Banner Grab",cat:"NET",api:"/api/banner",in:[{k:"host",l:"Host",p:"example.com"},{k:"port",l:"Port",p:"22"}]},
{n:13,name:"SSL Sertifika",cat:"NET",api:"/api/ssl",in:[{k:"host",l:"Host",p:"google.com"}]},
{n:14,name:"IPv6 Sorgu",cat:"NET",api:"/api/ipv6",in:[{k:"domain",l:"Domain",p:"google.com"}]},
{n:15,name:"HTTP Header",cat:"WEB",api:"/api/headers",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:16,name:"robots.txt",cat:"WEB",api:"/api/robots",in:[{k:"url",l:"Site",p:"example.com"}]},
{n:17,name:"sitemap.xml",cat:"WEB",api:"/api/sitemap",in:[{k:"url",l:"Site",p:"example.com"}]},
{n:18,name:"security.txt",cat:"WEB",api:"/api/sectxt",in:[{k:"url",l:"Site",p:"example.com"}]},
{n:19,name:"HTTP Methods",cat:"WEB",api:"/api/methods",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:20,name:"Subdomain Enum",cat:"WEB",api:"/api/subdomains",in:[{k:"domain",l:"Domain",p:"example.com"}]},
{n:21,name:"WAF Tespit",cat:"WEB",api:"/api/waf",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:22,name:"Güvenlik Header",cat:"WEB",api:"/api/headersec",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:23,name:"Cookie Analizi",cat:"WEB",api:"/api/cookie",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:24,name:"Redirect Zinciri",cat:"WEB",api:"/api/redirect",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:25,name:"CVE Arama",cat:"WEB",api:"/api/cve",in:[{k:"q",l:"Arama",p:"apache 2.4"}]},
{n:26,name:"Site Kopyala (HTML)",cat:"COPY",api:"/api/copy",in:[{k:"url",l:"URL",p:"example.com"}]},
{n:27,name:"Site Full İndir (ZIP)",cat:"COPY",api:"/api/copyfull",in:[{k:"url",l:"URL",p:"example.com"}]},
{n:28,name:"Sayfa Metni Çıkar",cat:"COPY",api:"/api/pagetext",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:29,name:"Kaynak Kod Görüntüle",cat:"COPY",api:"/api/viewsrc",in:[{k:"url",l:"URL",p:"https://example.com"}]},
{n:30,name:"Hash / Base64 / URL",cat:"CRYPTO",api:"/api/hash",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:31,name:"Hash Identifier",cat:"CRYPTO",api:"/api/hashid",in:[{k:"hash",l:"Hash",p:"5d41402abc4b2a76b9719d911017c592"}]},
{n:32,name:"Şifre Üretici",cat:"CRYPTO",api:"/api/passgen",in:[{k:"length",l:"Uzunluk",p:"20"},{k:"count",l:"Adet",p:"5"}]},
{n:33,name:"Şifre Gücü Analizi",cat:"CRYPTO",api:"/api/passstrength",in:[{k:"password",l:"Şifre",p:"Merhaba123!"}]},
{n:34,name:"JWT Decoder",cat:"CRYPTO",api:"/api/jwt",in:[{k:"jwt",l:"JWT",p:"eyJ..."}]},
{n:35,name:"Hex Enc/Dec",cat:"CRYPTO",api:"/api/hex",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:36,name:"ROT13 / Caesar",cat:"CRYPTO",api:"/api/rot13",in:[{k:"text",l:"Metin",p:"merhaba"},{k:"shift",l:"Shift",p:"13"}]},
{n:37,name:"Binary Enc/Dec",cat:"CRYPTO",api:"/api/binary",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:38,name:"Base32 Enc/Dec",cat:"CRYPTO",api:"/api/base32",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:39,name:"URL Enc/Dec",cat:"CRYPTO",api:"/api/urlencode",in:[{k:"text",l:"Metin",p:"merhaba dünya"}]},
{n:40,name:"HTML Entity Enc/Dec",cat:"CRYPTO",api:"/api/htmlentity",in:[{k:"text",l:"Metin",p:"<div>test</div>"}]},
{n:41,name:"Whois",cat:"RECON",api:"/api/whois",in:[{k:"domain",l:"Domain",p:"example.com"}]},
{n:42,name:"URL Parser",cat:"RECON",api:"/api/urlparse",in:[{k:"url",l:"URL",p:"https://example.com/path?q=1"}]},
{n:43,name:"Wayback Machine",cat:"RECON",api:"/api/wayback",in:[{k:"url",l:"URL",p:"example.com"}]},
{n:44,name:"Discord Username",cat:"RECON",api:"/api/discord",in:[{k:"username",l:"Username",p:"grego"}]},
{n:45,name:"Discord ID Sorgu",cat:"RECON",api:"/api/discordid",in:[{k:"id",l:"Discord ID (17-19 hane)",p:"1544616638895227004"}]},
{n:46,name:"GitHub Profil",cat:"RECON",api:"/api/github",in:[{k:"username",l:"Username",p:"torvalds"}]},
{n:47,name:"Reddit Profil",cat:"RECON",api:"/api/reddit",in:[{k:"username",l:"Username",p:"spez"}]},
{n:48,name:"DNS Zone Transfer",cat:"RECON",api:"/api/zonetr",in:[{k:"domain",l:"Domain",p:"example.com"}]},
{n:49,name:"QR Kod Üret",cat:"MISC",api:"/api/qr",in:[{k:"data",l:"İçerik",p:"https://example.com"}]},
{n:50,name:"Kısa Link Çöz",cat:"MISC",api:"/api/short",in:[{k:"url",l:"Kısa Link",p:"https://bit.ly/xyz"}]},
{n:51,name:"URL Kısalt",cat:"MISC",api:"/api/urlshort",in:[{k:"url",l:"Uzun URL",p:"https://example.com"}]},
{n:52,name:"UUID Üretici",cat:"MISC",api:"/api/uuid",in:[{k:"count",l:"Adet",p:"5"}]},
{n:53,name:"Sistem Bilgisi",cat:"MISC",api:"/api/sysinfo",in:[]},
{n:54,name:"JSON Formatla",cat:"MISC",api:"/api/jsonfmt",in:[{k:"text",l:"JSON",p:'{"a":1}',ta:1}]},
{n:55,name:"Metin Diff",cat:"MISC",api:"/api/diff",in:[{k:"a",l:"1. Metin",p:"a\\nb",ta:1},{k:"b",l:"2. Metin",p:"a\\nc",ta:1}]},
{n:56,name:"Rastgele UA",cat:"MISC",api:"/api/useragent",in:[{k:"count",l:"Adet",p:"10"}]},
{n:57,name:"Rastgele Email",cat:"MISC",api:"/api/emailgen",in:[{k:"count",l:"Adet",p:"5"}]},
{n:58,name:"Luhn Kart Kontrol",cat:"MISC",api:"/api/luhn",in:[{k:"number",l:"Kart No",p:"4111111111111111"}]},
{n:59,name:"IP:Port Ayrıştır",cat:"MISC",api:"/api/ipport",in:[{k:"text",l:"IP:Port",p:"8.8.8.8:53"}]},
{n:60,name:"Sahte Türk Numara",cat:"MISC",api:"/api/fakenum",in:[{k:"count",l:"Adet",p:"5"},{k:"operator",l:"Operatör (boş=rastgele)",p:"Turkcell"}]},
{n:61,name:"Sahte Türk IP",cat:"MISC",api:"/api/fakeip",in:[{k:"count",l:"Adet",p:"5"}]},
{n:62,name:"Sahte Kart Bilgisi",cat:"MISC",api:"/api/fakecard",in:[{k:"count",l:"Adet",p:"3"}]},
{n:63,name:"Sahte Türk Kimlik",cat:"MISC",api:"/api/faketc",in:[{k:"count",l:"Adet",p:"3"}]},
{n:64,name:"Lorem Ipsum",cat:"MISC",api:"/api/lorem",in:[{k:"count",l:"Paragraf",p:"3"}]},
{n:65,name:"Rastgele String",cat:"MISC",api:"/api/randstr",in:[{k:"length",l:"Uzunluk",p:"32"},{k:"count",l:"Adet",p:"5"}]},
{n:66,name:"Unix Timestamp",cat:"MISC",api:"/api/timestamp",in:[{k:"ts",l:"Unix ts (boş=şimdi)",p:""}]},
{n:67,name:"MIME Type Sorgu",cat:"MISC",api:"/api/mime",in:[{k:"ext",l:"Uzantı",p:"pdf"}]},
{n:68,name:"HTTP Status Kodları",cat:"MISC",api:"/api/httpstatus",in:[{k:"code",l:"Kod (boş=tümü)",p:"404"}]},
{n:69,name:"Chmod Hesapla",cat:"MISC",api:"/api/chmod",in:[{k:"perm",l:"İzin",p:"755"}]},
{n:70,name:"Port Info",cat:"MISC",api:"/api/portinfo",in:[{k:"port",l:"Port",p:"80"}]},
{n:71,name:"Base58 Enc/Dec",cat:"MISC",api:"/api/base58",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:72,name:"Octal Enc/Dec",cat:"MISC",api:"/api/octal",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:73,name:"Decimal Enc/Dec",cat:"MISC",api:"/api/decimal",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:74,name:"Reverse Text",cat:"MISC",api:"/api/reverse",in:[{k:"text",l:"Metin",p:"merhaba"}]},
{n:75,name:"Case Converter",cat:"MISC",api:"/api/case",in:[{k:"text",l:"Metin",p:"Merhaba Dünya"}]},
{n:76,name:"Word Count",cat:"MISC",api:"/api/wordcount",in:[{k:"text",l:"Metin",p:"merhaba dünya",ta:1}]},
{n:77,name:"Remove Duplicates",cat:"MISC",api:"/api/uniq",in:[{k:"text",l:"Satırlar",p:"a\\nb\\na\\nc",ta:1}]},
{n:78,name:"Sort Lines",cat:"MISC",api:"/api/sortlines",in:[{k:"text",l:"Satırlar",p:"c\\na\\nb",ta:1}]},

{n:79,name:"Vowels",cat:"MISC",api:"/api/extra/vowels",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:80,name:"Consonants",cat:"CRYPTO",api:"/api/extra/consonants",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:81,name:"Digitsum",cat:"OSINT",api:"/api/extra/digitsum",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:82,name:"Asciisum",cat:"MISC",api:"/api/extra/asciisum",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:83,name:"Unique Words",cat:"CRYPTO",api:"/api/extra/unique_words",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:84,name:"Avgword",cat:"OSINT",api:"/api/extra/avgword",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:85,name:"Longword",cat:"MISC",api:"/api/extra/longword",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:86,name:"Shortword",cat:"CRYPTO",api:"/api/extra/shortword",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:87,name:"Reverse Lines",cat:"OSINT",api:"/api/extra/reverse_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:88,name:"Reverse Each Line",cat:"MISC",api:"/api/extra/reverse_each_line",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:89,name:"Dedupe Words",cat:"CRYPTO",api:"/api/extra/dedupe_words",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:90,name:"Sort Words",cat:"OSINT",api:"/api/extra/sort_words",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:91,name:"Sort Words Rev",cat:"MISC",api:"/api/extra/sort_words_rev",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:92,name:"Lower Lines",cat:"CRYPTO",api:"/api/extra/lower_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:93,name:"Upper Lines",cat:"OSINT",api:"/api/extra/upper_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:94,name:"Title Lines",cat:"MISC",api:"/api/extra/title_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:95,name:"Trim Lines",cat:"CRYPTO",api:"/api/extra/trim_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:96,name:"Remove Vowels",cat:"OSINT",api:"/api/extra/remove_vowels",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:97,name:"Remove Digits",cat:"MISC",api:"/api/extra/remove_digits",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:98,name:"Remove Letters",cat:"CRYPTO",api:"/api/extra/remove_letters",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:99,name:"Remove Punct",cat:"OSINT",api:"/api/extra/remove_punct",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:100,name:"Only Ascii",cat:"MISC",api:"/api/extra/only_ascii",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:101,name:"Ascii Codes Hex",cat:"CRYPTO",api:"/api/extra/ascii_codes_hex",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:102,name:"Unicode Names",cat:"OSINT",api:"/api/extra/unicode_names",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:103,name:"Unicode Escape",cat:"MISC",api:"/api/extra/unicode_escape",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:104,name:"Json String",cat:"CRYPTO",api:"/api/extra/json_string",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:105,name:"Json Unstring",cat:"OSINT",api:"/api/extra/json_unstring",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:106,name:"B64Urlenc",cat:"MISC",api:"/api/extra/b64urlenc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:107,name:"B64Urldec",cat:"CRYPTO",api:"/api/extra/b64urldec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:108,name:"B85Enc",cat:"OSINT",api:"/api/extra/b85enc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:109,name:"B85Dec",cat:"MISC",api:"/api/extra/b85dec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:110,name:"A85Enc",cat:"CRYPTO",api:"/api/extra/a85enc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:111,name:"A85Dec",cat:"OSINT",api:"/api/extra/a85dec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:112,name:"Hexdec",cat:"MISC",api:"/api/extra/hexdec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:113,name:"Bindec",cat:"CRYPTO",api:"/api/extra/bindec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:114,name:"Octenc",cat:"OSINT",api:"/api/extra/octenc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:115,name:"Octdec",cat:"MISC",api:"/api/extra/octdec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:116,name:"Decimalenc",cat:"CRYPTO",api:"/api/extra/decimalenc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:117,name:"Decimaldec",cat:"OSINT",api:"/api/extra/decimaldec",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:118,name:"Sha224",cat:"MISC",api:"/api/extra/sha224",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:119,name:"Sha384",cat:"CRYPTO",api:"/api/extra/sha384",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:120,name:"Sha3 256",cat:"OSINT",api:"/api/extra/sha3_256",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:121,name:"Sha3 512",cat:"MISC",api:"/api/extra/sha3_512",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:122,name:"Blake2B",cat:"CRYPTO",api:"/api/extra/blake2b",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:123,name:"Blake2S",cat:"OSINT",api:"/api/extra/blake2s",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:124,name:"Token32",cat:"MISC",api:"/api/extra/token32",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:125,name:"Token64",cat:"CRYPTO",api:"/api/extra/token64",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:126,name:"Url Safe Token",cat:"OSINT",api:"/api/extra/url_safe_token",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:127,name:"Uuid Hex",cat:"MISC",api:"/api/extra/uuid_hex",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:128,name:"Uuid Int",cat:"CRYPTO",api:"/api/extra/uuid_int",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:129,name:"Timestamp Ms",cat:"OSINT",api:"/api/extra/timestamp_ms",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:130,name:"Utc Iso",cat:"MISC",api:"/api/extra/utc_iso",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:131,name:"Utc Date",cat:"CRYPTO",api:"/api/extra/utc_date",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:132,name:"Utc Time",cat:"OSINT",api:"/api/extra/utc_time",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:133,name:"Weekday",cat:"MISC",api:"/api/extra/weekday",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:134,name:"Week",cat:"CRYPTO",api:"/api/extra/week",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:135,name:"Year",cat:"OSINT",api:"/api/extra/year",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:136,name:"Month",cat:"MISC",api:"/api/extra/month",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:137,name:"Day",cat:"CRYPTO",api:"/api/extra/day",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:138,name:"Hour",cat:"OSINT",api:"/api/extra/hour",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:139,name:"Minute",cat:"MISC",api:"/api/extra/minute",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:140,name:"Second",cat:"CRYPTO",api:"/api/extra/second",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:141,name:"Ip Valid",cat:"OSINT",api:"/api/extra/ip_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:142,name:"Ipv4 Private",cat:"MISC",api:"/api/extra/ipv4_private",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:143,name:"Ipv4 Public",cat:"CRYPTO",api:"/api/extra/ipv4_public",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:144,name:"Ipv6 Private",cat:"OSINT",api:"/api/extra/ipv6_private",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:145,name:"Loopback",cat:"MISC",api:"/api/extra/loopback",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:146,name:"Multicast",cat:"CRYPTO",api:"/api/extra/multicast",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:147,name:"Port Valid",cat:"OSINT",api:"/api/extra/port_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:148,name:"Discord Id Valid",cat:"MISC",api:"/api/extra/discord_id_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:149,name:"Discord Created",cat:"CRYPTO",api:"/api/extra/discord_created",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:150,name:"Discord Default Avatar",cat:"OSINT",api:"/api/extra/discord_default_avatar",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:151,name:"Email Valid",cat:"MISC",api:"/api/extra/email_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:152,name:"Url Valid",cat:"CRYPTO",api:"/api/extra/url_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:153,name:"Domain Extract",cat:"OSINT",api:"/api/extra/domain_extract",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:154,name:"Query Params",cat:"MISC",api:"/api/extra/query_params",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:155,name:"Fragment Extract",cat:"CRYPTO",api:"/api/extra/fragment_extract",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:156,name:"Path Extract",cat:"OSINT",api:"/api/extra/path_extract",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:157,name:"Scheme Extract",cat:"MISC",api:"/api/extra/scheme_extract",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:158,name:"Hostname Valid",cat:"CRYPTO",api:"/api/extra/hostname_valid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:159,name:"Slug Strict",cat:"OSINT",api:"/api/extra/slug_strict",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:160,name:"Snake Strict",cat:"MISC",api:"/api/extra/snake_strict",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:161,name:"Kebab Strict",cat:"CRYPTO",api:"/api/extra/kebab_strict",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:162,name:"Dot Strict",cat:"OSINT",api:"/api/extra/dot_strict",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:163,name:"Collapse Newlines",cat:"MISC",api:"/api/extra/collapse_newlines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:164,name:"Collapse Spaces",cat:"CRYPTO",api:"/api/extra/collapse_spaces",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:165,name:"Remove Blank Lines",cat:"OSINT",api:"/api/extra/remove_blank_lines",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:166,name:"Pad Left",cat:"MISC",api:"/api/extra/pad_left",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:167,name:"Pad Right",cat:"CRYPTO",api:"/api/extra/pad_right",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:168,name:"Center20",cat:"OSINT",api:"/api/extra/center20",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:169,name:"Zfill20",cat:"MISC",api:"/api/extra/zfill20",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:170,name:"Repeat5",cat:"CRYPTO",api:"/api/extra/repeat5",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:171,name:"Repeat10",cat:"OSINT",api:"/api/extra/repeat10",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:172,name:"Char Frequency",cat:"MISC",api:"/api/extra/char_frequency",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:173,name:"Word Frequency",cat:"CRYPTO",api:"/api/extra/word_frequency",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:174,name:"Number List",cat:"OSINT",api:"/api/extra/number_list",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:175,name:"Number Sum",cat:"MISC",api:"/api/extra/number_sum",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:176,name:"Number Median",cat:"CRYPTO",api:"/api/extra/number_median",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:177,name:"Number Stdev",cat:"OSINT",api:"/api/extra/number_stdev",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:178,name:"Number Variance",cat:"MISC",api:"/api/extra/number_variance",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:179,name:"Number Range",cat:"CRYPTO",api:"/api/extra/number_range",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:180,name:"Is Even",cat:"OSINT",api:"/api/extra/is_even",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:181,name:"Is Odd",cat:"MISC",api:"/api/extra/is_odd",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:182,name:"Is Prime",cat:"CRYPTO",api:"/api/extra/is_prime",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:183,name:"Factorial",cat:"OSINT",api:"/api/extra/factorial",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:184,name:"Gcd Pair",cat:"MISC",api:"/api/extra/gcd_pair",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:185,name:"Lcm Pair",cat:"CRYPTO",api:"/api/extra/lcm_pair",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:186,name:"Percent Of",cat:"OSINT",api:"/api/extra/percent_of",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:187,name:"Regex Escape2",cat:"MISC",api:"/api/extra/regex_escape2",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:188,name:"Strip Tags2",cat:"CRYPTO",api:"/api/extra/strip_tags2",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:189,name:"Html Escape2",cat:"OSINT",api:"/api/extra/html_escape2",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:190,name:"Html Unescape2",cat:"MISC",api:"/api/extra/html_unescape2",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:191,name:"Nfkd",cat:"CRYPTO",api:"/api/extra/nfkd",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:192,name:"Nfc",cat:"OSINT",api:"/api/extra/nfc",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:193,name:"Casefold",cat:"MISC",api:"/api/extra/casefold",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:194,name:"Capitalize",cat:"CRYPTO",api:"/api/extra/capitalize",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:195,name:"Swapcase2",cat:"OSINT",api:"/api/extra/swapcase2",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:196,name:"Reverse Words",cat:"MISC",api:"/api/extra/reverse_words",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:197,name:"First Line",cat:"CRYPTO",api:"/api/extra/first_line",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:198,name:"Last Line",cat:"OSINT",api:"/api/extra/last_line",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:199,name:"Linecount Nonempty",cat:"MISC",api:"/api/extra/linecount_nonempty",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:200,name:"Byte Count Utf8",cat:"CRYPTO",api:"/api/extra/byte_count_utf8",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:201,name:"Byte Count Ascii",cat:"OSINT",api:"/api/extra/byte_count_ascii",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:202,name:"Entropy",cat:"MISC",api:"/api/extra/entropy",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:203,name:"Palindrome Clean",cat:"CRYPTO",api:"/api/extra/palindrome_clean",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:204,name:"Anagram Signature",cat:"OSINT",api:"/api/extra/anagram_signature",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:205,name:"Random Hex16",cat:"MISC",api:"/api/extra/random_hex16",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:206,name:"Random Hex32",cat:"CRYPTO",api:"/api/extra/random_hex32",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:207,name:"Random Url Token",cat:"OSINT",api:"/api/extra/random_url_token",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:208,name:"Random Uuid",cat:"MISC",api:"/api/extra/random_uuid",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:209,name:"Random Uuid Hex",cat:"CRYPTO",api:"/api/extra/random_uuid_hex",in:[{k:"text",l:"Girdi",p:"Örnek metin 123"}]},
{n:210,name:"Random Bytes16",cat:"OSINT",api:"/api/extra/random_bytes16",in:[{k:"text",l:"Girdi",p:"Örnek metin"}]},
{n:211,name:"Kullanıcıları Listele",cat:"ADMIN",api:"/api/admin/users",in:[]},
{n:212,name:"Site Rolü Ver / Al",cat:"ADMIN",api:"/api/admin/role",in:[{k:"username",l:"Kullanıcı",p:"kullaniciadi"},{k:"role",l:"Rol (vip/founder)",p:"vip"},{k:"action",l:"İşlem (grant/revoke)",p:"grant"}]},
{n:213,name:"Güvenli Logları Gör",cat:"ADMIN",api:"/api/admin/logs",in:[{k:"limit",l:"Satır",p:"100"}]},
];

const CATS={ALL:{n:"Tümü",i:"◈"},OSINT:{n:"OSINT",i:"◉"},NET:{n:"Ağ",i:"◐"},WEB:{n:"Web",i:"◑"},COPY:{n:"Kopya",i:"◒"},CRYPTO:{n:"Kripto",i:"◆"},RECON:{n:"Recon",i:"◇"},MISC:{n:"Araçlar",i:"○"},ADMIN:{n:"Yönetim",i:"🛡"}};

let curCat="ALL", lastResult=null, activeTool=null;

document.addEventListener("DOMContentLoaded",()=>{
  buildNav(); renderTools(); loadMe();
  document.getElementById("search").addEventListener("input",e=>renderTools(e.target.value));
  document.getElementById("copyBtn").onclick=copyRes;
  document.getElementById("closeBtn").onclick=()=>document.getElementById("result").classList.add("hide");
  document.getElementById("runBtn").onclick=runTool;
  document.addEventListener("keydown",e=>{if(e.key==="Escape")closeM();});
  document.addEventListener("click",function once(){
    const m=document.getElementById("bgMusic");
    if(m && m.paused){
      m.play().then(()=>{document.getElementById("musicBtn").textContent="⏸ Müziği Durdur";}).catch(()=>{});
    }
    document.removeEventListener("click",once);
  });
});

function toggleMusic(){
  const m=document.getElementById("bgMusic");
  const b=document.getElementById("musicBtn");
  if(m.paused){m.play().then(()=>{b.textContent="⏸ Müziği Durdur";}).catch(e=>console.log("müzik:",e));}
  else{m.pause();b.textContent="🔊 Müziği Çal";}
}

let isAdmin=false;
async function loadMe(){
  try{
    const r=await fetch("/api/whoami"); const d=await r.json();
    if(d.status==="ok"){
      document.getElementById("me").textContent=d.data.username+" • "+d.data.role;
      isAdmin=!!d.data.is_admin;
      document.getElementById("adminBadge").style.display=isAdmin?"inline-block":"none";
      buildNav(); renderTools(document.getElementById("search").value);
    }
  }catch(e){}
}
function visibleTools(){return isAdmin?TOOLS:TOOLS.filter(t=>t.cat!=="ADMIN");}
function setCatAdmin(){curCat="ADMIN";buildNav();renderTools();}

async function logout(){await fetch("/api/logout",{method:"POST"});location.href="/";}

function buildNav(){
  const nav=document.getElementById("nav"); nav.innerHTML="";
  const vt=visibleTools();
  Object.entries(CATS).forEach(([k,c])=>{
    if(k==="ADMIN" && !isAdmin) return;
    const cnt=k==="ALL"?vt.length:vt.filter(t=>t.cat===k).length;
    const b=document.createElement("button");
    b.className="nav-btn"+(k===curCat?" active":"");
    b.innerHTML=`<span>${c.i} ${c.n}</span><span class="nav-count">${cnt}</span>`;
    b.onclick=()=>{curCat=k;buildNav();renderTools();};
    nav.appendChild(b);
  });
}

function renderTools(f=""){
  const grid=document.getElementById("grid"); grid.innerHTML="";
  let list=visibleTools();
  if(curCat!=="ALL") list=list.filter(t=>t.cat===curCat);
  if(f){const q=f.toLowerCase();list=list.filter(t=>t.name.toLowerCase().includes(q)||t.cat.toLowerCase().includes(q));}
  if(!list.length){grid.innerHTML='<div class="empty" style="grid-column:1/-1">Bulunamadı</div>';return;}
  list.forEach((t,i)=>{
    const c=document.createElement("div"); c.className="tool"; c.style.animationDelay=(i*0.02)+"s";
    const num=document.createElement("div"); num.className="tool-num"; num.textContent="["+String(t.n).padStart(2,"0")+"]";
    const nm=document.createElement("div"); nm.className="tool-name"; nm.textContent=t.name;
    const ct=document.createElement("div"); ct.className="tool-cat"; ct.textContent=CATS[t.cat]?.n||t.cat;
    c.appendChild(num); c.appendChild(nm); c.appendChild(ct);
    c.onclick=()=>openTool(t);
    grid.appendChild(c);
  });
}

function openTool(t){
  activeTool=t;
  document.getElementById("mTitle").textContent="["+t.n+"] "+t.name;
  const b=document.getElementById("mBody"); b.innerHTML="";
  if(!t.in.length){const d=document.createElement("div");d.style.color="var(--dim)";d.style.textAlign="center";d.textContent="Giriş gerekmez";b.appendChild(d);}
  else{
    t.in.forEach(inp=>{
      const f=document.createElement("div"); f.className="field";
      const lb=document.createElement("label"); lb.textContent=inp.l;
      const tag=inp.ta?"textarea":"input";
      const el=document.createElement(tag); el.id="in_"+inp.k; el.placeholder=inp.p||"";
      f.appendChild(lb); f.appendChild(el); b.appendChild(f);
    });
  }
  document.getElementById("modal").classList.remove("hide");
}
function closeM(){document.getElementById("modal").classList.add("hide");activeTool=null;}

async function runTool(){
  if(!activeTool) return;
  const payload={};
  activeTool.in.forEach(i=>{const el=document.getElementById("in_"+i.k);payload[i.k]=el?el.value:"";});
  const btn=document.getElementById("runBtn"); btn.disabled=true; btn.innerHTML='<span class="spin"></span> ...';
  const tool={...activeTool}; closeM();
  try{
    const r=await fetch(tool.api,{method:"POST",headers:{"Content-Type":"application/json"},body:JSON.stringify(payload)});
    if(r.status===401){location.href="/";return;}
    const d=await r.json();
    showRes(tool.name,d);
    if(d.status==="ok") toast("Başarılı","success"); else toast(d.message||"Hata","error");
  }catch(e){showRes(tool.name,{status:"error",message:"Bağlantı: "+e.message});toast("Hata","error");}
  finally{btn.disabled=false;btn.textContent="ÇALIŞTIR";}
}

function showRes(title,data){
  lastResult=JSON.stringify(data,null,2);
  document.getElementById("rTitle").textContent=title;
  const b=document.getElementById("rBody"); b.innerHTML="";
  if(data.status==="error"){
    const d=document.createElement("div"); d.className="bad"; d.textContent="X "+data.message; b.appendChild(d);
  }else renderJSON(data.data,b,0);
  const p=document.getElementById("result"); p.classList.remove("hide");
  p.scrollIntoView({behavior:"smooth",block:"start"});
}

function renderProfileBox(obj,parent){
  const box=document.createElement("div");
  box.className="profile-box";

  if(obj._avatar){
    const wrap=document.createElement("div");
    wrap.style.textAlign="center";
    wrap.style.minWidth="140px";

    const av=document.createElement("img");
    av.className="profile-avatar";
    av.src=String(obj._avatar);
    av.alt="avatar";
    av.onerror=function(){this.style.display="none";};
    wrap.appendChild(av);

    const dlBtn=document.createElement("a");
    dlBtn.href=String(obj._avatar);
    dlBtn.download="avatar_"+(obj.id||"user")+".png";
    dlBtn.target="_blank";
    dlBtn.textContent="⬇ Avatar İndir";
    dlBtn.className="dl";
    dlBtn.style.display="block";
    dlBtn.style.marginTop="8px";
    dlBtn.style.fontSize="10px";
    wrap.appendChild(dlBtn);

    box.appendChild(wrap);
  }

  if(obj._banner){
    const wrap=document.createElement("div");
    wrap.style.flex="1";
    wrap.style.minWidth="200px";

    const bn=document.createElement("div");
    bn.className="profile-banner";

    const img=document.createElement("img");
    img.src=String(obj._banner);
    img.alt="banner";
    img.onerror=function(){this.parentElement.style.display="none";};
    bn.appendChild(img);
    wrap.appendChild(bn);

    const dlBtn=document.createElement("a");
    dlBtn.href=String(obj._banner);
    dlBtn.download="banner_"+(obj.id||"user")+".png";
    dlBtn.target="_blank";
    dlBtn.textContent="⬇ Banner İndir";
    dlBtn.className="dl";
    dlBtn.style.display="inline-block";
    dlBtn.style.marginTop="8px";
    dlBtn.style.fontSize="10px";
    wrap.appendChild(dlBtn);

    box.appendChild(wrap);
  }

  if(box.children.length) parent.appendChild(box);
}

function renderHesapBox(obj,parent){
  if(!obj["Hesap Bilgileri"]) return;
  const hb=obj["Hesap Bilgileri"];
  const box=document.createElement("div");
  box.className="hesap-box";
  const title=document.createElement("div");
  title.className="hesap-title";
  title.textContent="👤 Hesap Bilgileri";
  box.appendChild(title);

  Object.entries(hb).forEach(([k,v])=>{
    if(k==="Not") return;
    const row=document.createElement("div");
    row.className="hesap-row";
    const kk=document.createElement("span");
    kk.className="hesap-key";
    kk.textContent=k;
    const vv=document.createElement("span");
    vv.className="hesap-val";
    vv.textContent=String(v);
    row.appendChild(kk); row.appendChild(vv);
    box.appendChild(row);
  });

  if(hb["Not"]){
    const note=document.createElement("div");
    note.className="hesap-note";
    note.textContent=hb["Not"];
    box.appendChild(note);
  }

  parent.appendChild(box);
}

function renderJSON(obj,parent,depth){
  if(depth>6){const d=document.createElement("div");d.style.color="var(--dim)";d.textContent="...";parent.appendChild(d);return;}
  if(obj===null||obj===undefined){const d=document.createElement("div");d.className="v";d.textContent="-";parent.appendChild(d);return;}
  if(Array.isArray(obj)){
    if(!obj.length){const d=document.createElement("div");d.className="empty";d.textContent="(boş)";parent.appendChild(d);return;}
    obj.forEach((it,i)=>{
      const pad=document.createElement("div");pad.style.paddingLeft=(depth*14)+"px";
      if(typeof it==="object"&&it!==null){
        const h=document.createElement("div");h.className="info";h.textContent="["+i+"]";pad.appendChild(h);parent.appendChild(pad);
        renderJSON(it,parent,depth+1);
      }else{
        const l=document.createElement("div");l.className="line";const s=document.createElement("span");s.className="v";s.textContent=String(it);l.appendChild(s);pad.appendChild(l);parent.appendChild(pad);
      }
    });
  }else if(typeof obj==="object"){
    if(obj._avatar || obj._banner) renderProfileBox(obj,parent);
    if(obj["Hesap Bilgileri"]) renderHesapBox(obj,parent);

    Object.entries(obj).forEach(([k,v])=>{
      if(k==="_avatar"||k==="_banner"||k==="Hesap Bilgileri") return;
      const pad=document.createElement("div");pad.style.paddingLeft=(depth*14)+"px";
      if(typeof v==="object"&&v!==null){
        const kk=document.createElement("span");kk.className="k";kk.textContent=k;pad.appendChild(kk);pad.appendChild(document.createTextNode(":"));
        parent.appendChild(pad); renderJSON(v,parent,depth+1);
      }else{
        const l=document.createElement("div");l.className="line";
        const kk=document.createElement("span");kk.className="k";kk.textContent=k;l.appendChild(kk);
        l.appendChild(document.createTextNode(": "));
        if(k==="_code"){const cb=document.createElement("div");cb.className="code-box";cb.textContent=String(v);l.appendChild(cb);}
        else if(k==="profil_url"||k==="profil"){const a=document.createElement("a");a.className="dl";a.href=String(v);a.target="_blank";a.rel="noopener noreferrer";a.textContent="👤 DISCORD PROFİLİNİ AÇ";l.appendChild(a);}
        else if(k==="_download"){const a=document.createElement("a");a.className="dl";a.href=String(v);a.textContent="⬇ İNDİR";a.setAttribute("download","");l.appendChild(a);}
        else{
          const vv=document.createElement("span"); vv.className="v";
          if(v===true)vv.classList.add("ok");
          if(v===false)vv.classList.add("bad");
          vv.textContent=String(v); l.appendChild(vv);
        }
        pad.appendChild(l);parent.appendChild(pad);
      }
    });
  }else{
    const d=document.createElement("div");d.className="v";d.textContent=String(obj);parent.appendChild(d);
  }
}

function copyRes(){if(!lastResult)return;navigator.clipboard.writeText(lastResult);toast("Kopyalandı","success");}
function toast(m,t="success"){const el=document.getElementById("toast");el.textContent=m;el.className="toast show "+t;clearTimeout(el._t);el._t=setTimeout(()=>el.classList.remove("show"),2500);}
</script></body></html>
"""



@app.route("/discord/login")
@login_required
def discord_login():
    return err("Discord OAuth bu güvenli sürümde devre dışı", 410)

@app.route("/discord/callback")
def discord_callback():
    return err("Discord OAuth bu güvenli sürümde devre dışı", 410)

@app.route("/api/discord/me", methods=["POST"])
@login_required
def api_discord_me():
    return err("Discord OAuth bu güvenli sürümde devre dışı", 410)

@app.route("/api/whoami")
@login_required
def api_whoami_new():
    username = session.get("username", "?")
    role = session.get("role", "user")
    if not role:
        with db_conn() as c:
            row = c.execute("SELECT role FROM users WHERE username=?", (username,)).fetchone()
            role = row["role"] if row else "user"
    is_admin = _current_user_is_admin()
    return ok({
        "username": username,
        "role": "admin" if is_admin else role,
        "is_admin": is_admin,
    })

@app.route("/api/admin/users", methods=["POST"])
@admin_required
def api_admin_users():
    with db_conn() as c:
        rows = c.execute("SELECT id,username,created_at,role FROM users ORDER BY id DESC LIMIT 500").fetchall()
    return ok([dict(r) for r in rows])

@app.route("/api/admin/role", methods=["POST"])
@admin_required
def api_admin_role():
    d = request.get_json(silent=True) or {}
    username = str(d.get("username", "")).strip()
    role = str(d.get("role", "user")).strip().lower()
    action = str(d.get("action", "grant")).strip().lower()
    if not username or role not in {"vip", "founder"} or action not in {"grant", "revoke"}:
        return err("username + role(vip/founder) + action(grant/revoke) gerekli")
    target_role = role if action == "grant" else "user"
    with db_conn() as c:
        row = c.execute("SELECT username,role FROM users WHERE username=?", (username,)).fetchone()
        if not row:
            return err("Kullanıcı bulunamadı", 404)
        c.execute("UPDATE users SET role=? WHERE username=?", (target_role, username))
        c.commit()
    log_event("ROLE_CHANGE", f"target={username} role={role} action={action}")
    return ok({"username": username, "role": target_role}, "Rol güncellendi")

@app.route("/api/admin/logs", methods=["POST"])
@admin_required
def api_admin_logs():
    try:
        limit = max(1, min(int((request.get_json(silent=True) or {}).get("limit", 100)), 500))
    except Exception:
        limit = 100
    try:
        lines = LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()[-limit:]
    except Exception:
        lines = []
    return ok({"count": len(lines), "logs": lines})

@app.route("/")
def index():
    if session.get("logged_in"): return redirect(url_for("app_page"))
    return Response(HTML_LOGIN, mimetype="text/html; charset=utf-8")


@app.route("/app")
def app_page():
    if not session.get("logged_in"): return redirect(url_for("index"))
    return Response(HTML_APP, mimetype="text/html; charset=utf-8")


@app.route("/favicon.ico")
def favicon(): return Response(status=204)


@app.route("/api/register", methods=["POST"])
@limiter.limit("5 per minute")
def api_register():
    try:
        d=request.get_json(silent=True) or {}
        u=str(d.get("username","")).strip()
        pw=str(d.get("password",""))
        if not re.fullmatch(r"[A-Za-z0-9_.-]{3,32}",u): return err("Geçersiz kullanıcı adı")
        if len(pw)<8 or len(pw)>200: return err("Şifre 8-200 karakter olmalı")
        with db_conn() as c:
            c.execute("INSERT INTO users(username,password_hash,created_at,role) VALUES(?,?,?,?)",(u,generate_password_hash(pw),datetime.now().isoformat(timespec="seconds"),"user"))
            c.commit()
        return ok({"username":u},"Kayıt başarılı, şimdi giriş yapabilirsin")
    except sqlite3.IntegrityError:
        return err("Bu kullanıcı adı zaten kayıtlı")
    except Exception:
        return err("Kayıt sırasında hata oluştu")


@app.route("/api/login", methods=["POST"])
@limiter.limit("10 per minute")
def api_login():
    try:
        d = request.get_json(silent=True) or {}
        u = d.get("username", "").strip()
        p = d.get("password", "")
        if not u or not p:
            log_event("LOGIN_FAIL", "reason=empty")
            return err("Kullanıcı adı veya şifre hatalı")
        valid = (u == ADMIN_USER and check_password_hash(ADMIN_HASH, p))
        if not valid:
            with db_conn() as c:
                row=c.execute("SELECT password_hash FROM users WHERE username=?",(u,)).fetchone()
            valid = bool(row and check_password_hash(row["password_hash"], p))
        if not valid:
            log_event("LOGIN_FAIL", "reason=invalid")
            return err("Kullanıcı adı veya şifre hatalı")
        session.clear(); session["logged_in"] = True; session["username"] = u
        with db_conn() as c:
            row = c.execute("SELECT role FROM users WHERE username=?", (u,)).fetchone()
        session["role"] = ("admin" if u == ADMIN_USER and ADMIN_USER else (row["role"] if row else "user"))
        log_event("LOGIN_OK", f"user={u}")
        return ok({"username": u}, "Giriş başarılı")
    except Exception as e:
        log_event("LOGIN_ERR", f"err={type(e).__name__}")
        return err("Giriş hatası")


@app.route("/api/logout", methods=["POST"])
def api_logout():
    log_event("LOGOUT"); session.clear()
    return ok({}, "Çıkış")




@app.route("/api/ping", methods=["POST"])
@login_required
def api_ping(): return ok({"pong": True})


# ==================== OSINT ====================
@app.route("/api/ip", methods=["POST"])
@login_required
@limiter.limit("30 per minute")
def api_ip():
    try:
        d = request.get_json(silent=True) or {}
        ip = d.get("ip", "").strip()
        if ip and not re.match(r'^[a-fA-F0-9.:]+$', ip): return err("Geçersiz IP")
        r = safe_get(f"http://ip-api.com/json/{ip}?lang=tr", allow_http=True)
        j = r.json()
        return ok(j) if j.get("status") == "success" else err(j.get("message", "Hata"))
    except Exception as e: return err(f"IP: {str(e)[:120]}")


@app.route("/api/cidr", methods=["POST"])
@login_required
def api_cidr():
    try:
        d = request.get_json(silent=True) or {}
        net = ipaddress.ip_network(d.get("cidr", "").strip(), strict=False)
        if net.num_addresses > 65536: return err("Ağ çok büyük (max /16)")
        return ok({"Network": str(net.network_address), "Broadcast": str(net.broadcast_address),
                   "Netmask": str(net.netmask), "Host Count": net.num_addresses - 2,
                   "Version": f"IPv{net.version}"})
    except Exception as e: return err(f"CIDR: {str(e)[:120]}")


@app.route("/api/mac", methods=["POST"])
@login_required
def api_mac():
    try:
        d = request.get_json(silent=True) or {}
        mac = d.get("mac", "").strip().upper().replace("-", ":")
        if not re.match(r'^[0-9A-F:]{6,20}$', mac): return err("Geçersiz MAC")
        r = safe_get(f"https://api.macvendors.com/{mac}")
        return ok({"Üretici": r.text}) if r.status_code == 200 else err("Bulunamadı")
    except Exception as e: return err(f"MAC: {str(e)[:120]}")


@app.route("/api/email", methods=["POST"])
@login_required
@limiter.limit("20 per minute")
def api_email():
    try:
        d = request.get_json(silent=True) or {}
        q = d.get("q", "").strip()
        if not q or len(q) > 100: return err("Geçersiz girdi")
        result = {"input": q, "found": []}
        if "@" in q:
            h = hashlib.md5(q.lower().encode()).hexdigest()
            try:
                r = safe_get(f"https://www.gravatar.com/avatar/{h}?d=404")
                result["Gravatar"] = "VAR" if r.status_code == 200 else "yok"
            except Exception: pass
        uname = q.split("@")[0] if "@" in q else q
        if re.match(r'^[a-zA-Z0-9_.-]+$', uname):
            try:
                r = safe_get(f"https://api.github.com/users/{uname}")
                if r.status_code == 200:
                    x = r.json()
                    result["found"].append({"site":"GitHub","url":x.get("html_url"),"name":x.get("name"),"bio":x.get("bio")})
            except Exception: pass
            try:
                r = safe_get(f"https://www.reddit.com/user/{uname}/about.json")
                if r.status_code == 200:
                    x = r.json().get("data", {})
                    if x.get("name"): result["found"].append({"site":"Reddit","url":f"https://reddit.com/u/{x.get('name')}"})
            except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Email: {str(e)[:120]}")


@app.route("/api/phone", methods=["POST"])
@login_required
def api_phone():
    try:
        d = request.get_json(silent=True) or {}
        num = d.get("num", "").strip()
        if not re.match(r'^\+?[0-9]{5,20}$', num): return err("Geçersiz numara")
        return ok({"Numara": num, "Info": "Numverify API key gerekli", "Alternatif": f"https://www.numlookup.com/{num}"})
    except Exception as e: return err(f"Telefon: {str(e)[:120]}")


@app.route("/api/usercheck", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_usercheck():
    try:
        d = request.get_json(silent=True) or {}
        uname = d.get("username", "").strip()
        if not uname or not re.match(r'^[a-zA-Z0-9_.-]{1,50}$', uname):
            return err("Geçersiz kullanıcı adı")
        SITES = [
            ("GitHub", f"https://github.com/{uname}"),("Reddit", f"https://www.reddit.com/user/{uname}"),
            ("Twitter/X", f"https://x.com/{uname}"),("Instagram", f"https://instagram.com/{uname}"),
            ("TikTok", f"https://tiktok.com/@{uname}"),("YouTube", f"https://youtube.com/@{uname}"),
            ("Twitch", f"https://twitch.tv/{uname}"),("Steam", f"https://steamcommunity.com/id/{uname}"),
            ("Spotify", f"https://open.spotify.com/user/{uname}"),("Pinterest", f"https://pinterest.com/{uname}"),
            ("Medium", f"https://medium.com/@{uname}"),("DeviantArt", f"https://{uname}.deviantart.com"),
            ("Flickr", f"https://flickr.com/people/{uname}"),("Vimeo", f"https://vimeo.com/{uname}"),
            ("SoundCloud", f"https://soundcloud.com/{uname}"),("Telegram", f"https://t.me/{uname}"),
            ("GitLab", f"https://gitlab.com/{uname}"),("BitBucket", f"https://bitbucket.org/{uname}"),
            ("DockerHub", f"https://hub.docker.com/u/{uname}"),("npm", f"https://www.npmjs.com/~{uname}"),
            ("PyPI", f"https://pypi.org/user/{uname}"),("HackerNews", f"https://news.ycombinator.com/user?id={uname}"),
            ("Keybase", f"https://keybase.io/{uname}"),("CodePen", f"https://codepen.io/{uname}"),
            ("Replit", f"https://replit.com/@{uname}"),("About.me", f"https://about.me/{uname}"),
            ("Behance", f"https://behance.net/{uname}"),("Dribbble", f"https://dribbble.com/{uname}"),
            ("ArtStation", f"https://artstation.com/{uname}"),("Fiverr", f"https://fiverr.com/{uname}"),
            ("Etsy", f"https://etsy.com/shop/{uname}"),("Mastodon.social", f"https://mastodon.social/@{uname}"),
            ("Linktree", f"https://linktr.ee/{uname}"),("Roblox", f"https://www.roblox.com/user.aspx?username={uname}"),
            ("Xbox", f"https://xboxgamertag.com/search/{uname}"),("PSN", f"https://psnprofiles.com/{uname}"),
            ("Patreon", f"https://patreon.com/{uname}"),("Ko-fi", f"https://ko-fi.com/{uname}"),
            ("BuyMeACoffee", f"https://buymeacoffee.com/{uname}"),("ProductHunt", f"https://producthunt.com/@{uname}"),
            ("Scribd", f"https://scribd.com/{uname}"),("Mixcloud", f"https://mixcloud.com/{uname}"),
            ("Bandcamp", f"https://bandcamp.com/{uname}"),("LastFm", f"https://last.fm/user/{uname}"),
            ("Goodreads", f"https://goodreads.com/{uname}"),("Letterboxd", f"https://letterboxd.com/{uname}"),
            ("MyAnimeList", f"https://myanimelist.net/profile/{uname}"),("Wattpad", f"https://wattpad.com/user/{uname}"),
            ("Imgur", f"https://imgur.com/user/{uname}"),("9GAG", f"https://9gag.com/u/{uname}"),
            ("Tumblr", f"https://{uname}.tumblr.com"),("Disqus", f"https://disqus.com/by/{uname}"),
            ("SlideShare", f"https://slideshare.net/{uname}"),("FanFiction", f"https://fanfiction.net/u/{uname}"),
            ("ArchiveOfOurOwn", f"https://archiveofourown.org/users/{uname}"),("EpicGames", f"https://fortnitetracker.com/profile/all/{uname}"),
            ("StackOverflow", f"https://stackoverflow.com/users/filter?search={uname}"),("Duolingo", f"https://duolingo.com/profile/{uname}"),
            ("Venmo", f"https://venmo.com/{uname}"),("CashApp", f"https://cash.app/${uname}"),
        ]
        found = []; notfound = []; errors = []
        def check(item):
            name, url = item
            try:
                r = requests.head(url, headers=HEADERS, timeout=6, allow_redirects=True, verify=True)
                if r.status_code == 200: found.append({"site": name, "url": url})
                elif r.status_code in (301, 302, 403): found.append({"site": name, "url": url, "status": r.status_code})
                else: notfound.append(name)
            except Exception: errors.append(name)
        with concurrent.futures.ThreadPoolExecutor(max_workers=15) as ex:
            list(ex.map(check, SITES))
        found.sort(key=lambda x: x["site"])
        return ok({"username": uname, "total_checked": len(SITES), "found": found,
                   "not_found_count": len(notfound), "errors_count": len(errors)})
    except Exception as e: return err(f"UserCheck: {str(e)[:150]}")


# ==================== NET ====================
@app.route("/api/dns", methods=["POST"])
@login_required
@limiter.limit("30 per minute")
def api_dns():
    try:
        d = request.get_json(silent=True) or {}
        dom = d.get("domain", "").strip()
        if not dom or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', dom): return err("Geçersiz domain")
        if not HAS_DNS: return err("dnspython yok")
        records = {}
        for t in ["A","AAAA","MX","NS","TXT","CNAME","SOA"]:
            try:
                ans = dns.resolver.resolve(dom, t, lifetime=5)
                records[t] = [a.to_text() for a in ans][:20]
            except Exception: pass
        return ok(records) if records else err("Kayıt yok")
    except Exception as e: return err(f"DNS: {str(e)[:120]}")


@app.route("/api/rdns", methods=["POST"])
@login_required
def api_rdns():
    try:
        d = request.get_json(silent=True) or {}
        ip = d.get("ip", "").strip()
        try: ipaddress.ip_address(ip)
        except Exception: return err("Geçersiz IP")
        return ok({"Hostname": socket.gethostbyaddr(ip)[0]})
    except socket.herror: return err("PTR yok")
    except Exception as e: return err(f"rDNS: {str(e)[:120]}")


@app.route("/api/trace", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_trace():
    try:
        d = request.get_json(silent=True) or {}
        host = d.get("host", "").strip()
        if not host or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', host): return err("Geçersiz host")
        cmd = ["tracert", "-h", "15", host] if os.name == "nt" else ["traceroute", "-m", "15", host]
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=45, shell=False)
        return ok({"_code": (r.stdout or "(çıktı yok)")[:5000]})
    except subprocess.TimeoutExpired: return err("Zaman aşımı")
    except Exception as e: return err(f"Trace: {str(e)[:120]}")


@app.route("/api/portscan", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_portscan():
    try:
        d = request.get_json(silent=True) or {}
        host = d.get("host", "").strip()
        rng = d.get("range", "").strip()
        if not host or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', host): return err("Geçersiz host")
        if rng and "-" in rng:
            a, b = rng.split("-"); a, b = int(a), int(b)
            if a < 1 or b > 65535 or b - a > 1000: return err("Port aralığı geçersiz (max 1000)")
            ports = list(range(a, b + 1))
        else:
            ports = [21,22,23,25,53,80,110,143,443,445,993,995,1433,1521,3306,3389,5432,5900,6379,8080,8443,27017]
        try: ip = socket.gethostbyname(host)
        except socket.gaierror: return err("Host çözümlenemedi")
        open_ports = []
        def scan(p):
            s = socket.socket(); s.settimeout(0.6)
            try:
                if s.connect_ex((ip, p)) == 0:
                    try: svc = socket.getservbyport(p, "tcp")
                    except Exception: svc = "?"
                    open_ports.append({"port": p, "service": svc})
            except Exception: pass
            finally:
                try: s.close()
                except Exception: pass
        with concurrent.futures.ThreadPoolExecutor(max_workers=80) as ex:
            list(ex.map(scan, ports))
        open_ports.sort(key=lambda x: x["port"])
        return ok({"ip": ip, "open": open_ports, "total": len(ports)})
    except Exception as e: return err(f"Portscan: {str(e)[:120]}")


@app.route("/api/banner", methods=["POST"])
@login_required
def api_banner():
    try:
        d = request.get_json(silent=True) or {}
        host = d.get("host", "").strip()
        port = int(d.get("port", 22) or 22)
        if not host or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', host): return err("Geçersiz host")
        if port < 1 or port > 65535: return err("Geçersiz port")
        s = socket.socket(); s.settimeout(5)
        try:
            s.connect((host, port)); s.send(b"\r\n"); data = s.recv(2048)
        finally: s.close()
        return ok({"banner": (data.decode(errors="ignore") or "(boş)")[:1000]})
    except socket.timeout: return err("Zaman aşımı")
    except Exception as e: return err(f"Banner: {str(e)[:120]}")


@app.route("/api/ssl", methods=["POST"])
@login_required
def api_ssl():
    try:
        d = request.get_json(silent=True) or {}
        host = d.get("host", "").strip().replace("https://", "").split("/")[0]
        if not host or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', host): return err("Geçersiz host")
        ctx = ssl.create_default_context()
        with ctx.wrap_socket(socket.socket(), server_hostname=host) as s:
            s.settimeout(10); s.connect((host, 443)); c = s.getpeercert()
        return ok({k: str(v) for k, v in c.items()})
    except Exception as e: return err(f"SSL: {str(e)[:120]}")


@app.route("/api/ipv6", methods=["POST"])
@login_required
def api_ipv6():
    try:
        d = request.get_json(silent=True) or {}
        dom = d.get("domain", "").strip()
        if not dom or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', dom): return err("Geçersiz")
        r = safe_get(f"https://dns.google/resolve?name={urllib.parse.quote(dom)}&type=AAAA")
        return ok([a.get("data") for a in r.json().get("Answer", [])])
    except Exception as e: return err(f"IPv6: {str(e)[:120]}")


# ==================== WEB ====================
@app.route("/api/headers", methods=["POST"])
@login_required
@limiter.limit("20 per minute")
def api_headers():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True)
        return ok({"Status": r.status_code, "URL": r.url, "Headers": dict(r.headers)})
    except Exception as e: return err(f"Header: {str(e)[:120]}")


@app.route("/api/robots", methods=["POST"])
@login_required
def api_robots():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip().replace("https://", "").replace("http://", "")
        if not re.match(r'^[a-zA-Z0-9.-]{1,253}', url): return err("Geçersiz")
        r = safe_get(f"https://{url}/robots.txt", allow_redirects=True)
        return ok({"status": r.status_code, "content": r.text[:8000]})
    except Exception as e: return err(f"robots: {str(e)[:120]}")


@app.route("/api/sitemap", methods=["POST"])
@login_required
def api_sitemap():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip().replace("https://", "").replace("http://", "")
        if not re.match(r'^[a-zA-Z0-9.-]{1,253}', url): return err("Geçersiz")
        r = safe_get(f"https://{url}/sitemap.xml", allow_redirects=True)
        return ok({"status": r.status_code, "content": r.text[:8000]})
    except Exception as e: return err(f"sitemap: {str(e)[:120]}")


@app.route("/api/sectxt", methods=["POST"])
@login_required
def api_sectxt():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip().replace("https://", "").replace("http://", "")
        if not re.match(r'^[a-zA-Z0-9.-]{1,253}', url): return err("Geçersiz")
        for path in ["/.well-known/security.txt", "/security.txt"]:
            try:
                r = safe_get(f"https://{url}{path}", allow_redirects=True)
                if r.status_code == 200: return ok({"path": path, "content": r.text[:5000]})
            except Exception: pass
        return err("security.txt yok")
    except Exception as e: return err(f"sectxt: {str(e)[:120]}")


@app.route("/api/methods", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_methods():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        ok_, msg = validate_url(url, allow_http=True)
        if not ok_: return err(msg)
        results = {}
        for m in ["GET","POST","PUT","DELETE","OPTIONS","HEAD","PATCH"]:
            try:
                r = requests.request(m, url, timeout=6, allow_redirects=False, verify=True, headers=HEADERS)
                results[m] = r.status_code
            except Exception: results[m] = "hata"
        return ok(results)
    except Exception as e: return err(f"Methods: {str(e)[:120]}")


@app.route("/api/subdomains", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_subdomains():
    try:
        d = request.get_json(silent=True) or {}
        dom = d.get("domain", "").strip()
        if not dom or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', dom): return err("Geçersiz")
        subs = ["www","mail","ftp","api","dev","test","staging","admin","blog","shop","app","m","mobile","cdn","static","img","images","docs","support","help","forum","secure","vpn","portal","git","jenkins"]
        found = []
        def check(s):
            host = f"{s}.{dom}"
            try:
                ip = socket.gethostbyname(host)
                found.append({"subdomain": host, "ip": ip})
            except Exception: pass
        with concurrent.futures.ThreadPoolExecutor(max_workers=20) as ex:
            list(ex.map(check, subs))
        found.sort(key=lambda x: x["subdomain"])
        return ok(found)
    except Exception as e: return err(f"Subdomain: {str(e)[:120]}")


@app.route("/api/waf", methods=["POST"])
@login_required
def api_waf():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True)
        server = r.headers.get("Server", "?")
        waf_list = {"cloudflare":"Cloudflare","sucuri":"Sucuri","akamai":"Akamai","incapsula":"Incapsula","f5":"F5","awselb":"AWS ELB"}
        found = "Bulunamadı"
        for k, v in waf_list.items():
            if k in server.lower(): found = v; break
        return ok({"Server": server, "WAF": found})
    except Exception as e: return err(f"WAF: {str(e)[:120]}")


@app.route("/api/headersec", methods=["POST"])
@login_required
def api_headersec():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True)
        checks = ["Strict-Transport-Security","Content-Security-Policy","X-Frame-Options","X-Content-Type-Options","Referrer-Policy","Permissions-Policy"]
        return ok({c: (r.headers[c][:80] if c in r.headers else "YOK") for c in checks})
    except Exception as e: return err(f"HeaderSec: {str(e)[:120]}")


@app.route("/api/cookie", methods=["POST"])
@login_required
def api_cookie():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True)
        return ok([{"name": c.name, "value": c.value[:80], "domain": c.domain} for c in r.cookies])
    except Exception as e: return err(f"Cookie: {str(e)[:120]}")


@app.route("/api/redirect", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_redirect():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True)
        chain = [{"status": h.status_code, "url": h.url} for h in r.history]
        chain.append({"status": r.status_code, "url": r.url, "final": True})
        return ok(chain)
    except Exception as e: return err(f"Redirect: {str(e)[:120]}")


@app.route("/api/cve", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_cve():
    try:
        d = request.get_json(silent=True) or {}
        q = d.get("q", "").strip()
        if not q or len(q) > 100: return err("Geçersiz")
        r = safe_get("https://services.nvd.nist.gov/rest/json/cves/2.0",
                     params={"keywordSearch": q, "resultsPerPage": 15}, timeout=25)
        result = []
        for it in r.json().get("vulnerabilities", [])[:15]:
            c = it["cve"]
            desc = c.get("descriptions", [{}])[0].get("value", "")[:200]
            result.append({"id": c["id"], "description": desc})
        return ok(result)
    except Exception as e: return err(f"CVE: {str(e)[:120]}")


# ==================== COPY ====================
@app.route("/api/copy", methods=["POST"])
@login_required
@limiter.limit("5 per minute")
def api_copy():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        ok_, msg = validate_url(url, allow_http=True)
        if not ok_: return err(msg)
        r = safe_get(url, allow_http=True, allow_redirects=True, timeout=15)
        html = r.text[:500000]
        if HAS_BS4:
            try: html = BeautifulSoup(html, "html.parser").prettify()
            except Exception: pass
        host = (urllib.parse.urlparse(url).hostname or "site").replace(".", "_")
        fname = f"index_{host}_{secrets.token_hex(6)}.html"
        fn = TEMP_DIR / fname
        with open(fn, "w", encoding="utf-8") as f: f.write(html)
        return ok({"URL": url, "Status": r.status_code, "Boyut": f"{len(html)} byte",
                   "_download": f"/download/{fname}", "İlk 500": html[:500]})
    except Exception as e: return err(f"Kopyala: {str(e)[:120]}")


@app.route("/api/copyfull", methods=["POST"])
@login_required
@limiter.limit("3 per minute")
def api_copyfull():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        ok_, msg = validate_url(url, allow_http=True)
        if not ok_: return err(msg)
        host = (urllib.parse.urlparse(url).hostname or "site").replace(".", "_")
        out_dir = TEMP_DIR / f"site_{host}_{secrets.token_hex(6)}"
        out_dir.mkdir(exist_ok=True)
        saved = 0; errors = 0
        base = safe_get(url, allow_http=True, allow_redirects=True, timeout=20)
        html = base.text[:2000000]
        with open(out_dir / "index.html", "w", encoding="utf-8") as f: f.write(html)
        saved += 1
        if HAS_BS4:
            soup = BeautifulSoup(html, "html.parser")
            assets = set(); pages = set()
            for tag, attr in [("link", "href"), ("script", "src"), ("img", "src")]:
                for el in soup.find_all(tag):
                    v = el.get(attr)
                    if not v or v.startswith(("data:", "javascript:", "#")): continue
                    full = urllib.parse.urljoin(url, v)
                    if urllib.parse.urlparse(full).hostname == urllib.parse.urlparse(url).hostname:
                        assets.add(full)
            for a in soup.find_all("a", href=True)[:25]:
                h = a["href"]
                if h.startswith("/") or (h.startswith("http") and host.replace("_", ".") in h):
                    pages.add(urllib.parse.urljoin(url, h))
            def fetch_asset(u):
                nonlocal saved, errors
                try:
                    rr = safe_get(u, allow_http=True, allow_redirects=True, timeout=10)
                    if rr.status_code != 200: errors += 1; return
                    path = urllib.parse.urlparse(u).path.lstrip("/") or "asset_" + secrets.token_hex(4)
                    if len(path) > 200: path = path[-200:]
                    target = out_dir / path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with open(target, "wb") as f: f.write(rr.content[:5000000])
                    saved += 1
                except Exception: errors += 1
            def fetch_page(u):
                nonlocal saved, errors
                try:
                    rr = safe_get(u, allow_http=True, allow_redirects=True, timeout=10)
                    if rr.status_code != 200: errors += 1; return
                    path = urllib.parse.urlparse(u).path.strip("/").replace("/", "_") or "page"
                    if not path.endswith(".html"): path += ".html"
                    if len(path) > 200: path = path[-200:]
                    with open(out_dir / path, "w", encoding="utf-8") as f: f.write(rr.text[:2000000])
                    saved += 1
                except Exception: errors += 1
            with concurrent.futures.ThreadPoolExecutor(max_workers=15) as ex:
                list(ex.map(fetch_asset, list(assets)[:80]))
                list(ex.map(fetch_page, list(pages)[:25]))
        zip_path = shutil.make_archive(str(out_dir), "zip", str(out_dir))
        zip_name = Path(zip_path).name
        return ok({"URL": url, "Kaydedilen": saved, "Hata": errors,
                   "ZIP": zip_name, "_download": f"/download/{zip_name}"})
    except Exception as e: return err(f"CopyFull: {str(e)[:150]}")


@app.route("/api/viewsrc", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_viewsrc():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True, timeout=15)
        return ok({"URL": url, "Total Bytes": len(r.text), "_code": r.text[:8000]})
    except Exception as e: return err(f"Viewsrc: {str(e)[:120]}")


@app.route("/api/pagetext", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_pagetext():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url", "").strip()
        if not url.startswith(("http://", "https://")): url = "https://" + url
        r = safe_get(url, allow_redirects=True, timeout=15)
        if HAS_BS4:
            soup = BeautifulSoup(r.text[:500000], "html.parser")
            for s in soup(["script","style"]): s.decompose()
            text = soup.get_text("\n", strip=True)
        else: text = re.sub(r'<[^>]+>', '', r.text[:500000])
        return ok({"URL": url, "Metin": text[:5000]})
    except Exception as e: return err(f"PageText: {str(e)[:120]}")


# ==================== CRYPTO ====================
@app.route("/api/hash", methods=["POST"])
@login_required
def api_hash():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text", "")[:10000]
        result = {}
        for a in ["md5","sha1","sha256","sha512"]:
            result[a.upper()] = hashlib.new(a, t.encode()).hexdigest()
        result["Base64"] = base64.b64encode(t.encode()).decode()
        result["URL"] = urllib.parse.quote(t)
        try: result["HMAC-SHA256"] = hmac.new(b"key", t.encode(), hashlib.sha256).hexdigest()
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Hash: {str(e)[:120]}")


@app.route("/api/hashid", methods=["POST"])
@login_required
def api_hashid():
    try:
        d = request.get_json(silent=True) or {}
        h = d.get("hash", "").strip()
        if not re.match(r'^[a-fA-F0-9]+$', h): return err("Sadece hex")
        n = len(h); results = []
        if n == 32: results.append("MD5 / NTLM / MD4")
        if n == 40: results.append("SHA-1 / MySQL5 / RIPEMD-160")
        if n == 56: results.append("SHA-224")
        if n == 64: results.append("SHA-256 / Keccak-256")
        if n == 96: results.append("SHA-384")
        if n == 128: results.append("SHA-512 / Whirlpool")
        if not results: results.append("Bilinmeyen")
        return ok({"length": n, "olası": results})
    except Exception as e: return err(f"HashID: {str(e)[:120]}")


@app.route("/api/passgen", methods=["POST"])
@login_required
def api_passgen():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("length", 20) or 20)
        except Exception: n = 20
        try: c = int(d.get("count", 5) or 5)
        except Exception: c = 5
        n = max(4, min(n, 256)); c = max(1, min(c, 50))
        chars = string.ascii_letters + string.digits + "!@#$%^&*()-_=+"
        return ok([''.join(secrets.choice(chars) for _ in range(n)) for _ in range(c)])
    except Exception as e: return err(f"Passgen: {str(e)[:120]}")


@app.route("/api/passstrength", methods=["POST"])
@login_required
def api_passstrength():
    try:
        import math
        d = request.get_json(silent=True) or {}
        p = d.get("password", "")
        if not p: return err("Şifre gerekli")
        charset = 0
        if any(c.islower() for c in p): charset += 26
        if any(c.isupper() for c in p): charset += 26
        if any(c.isdigit() for c in p): charset += 10
        if any(c in "!@#$%^&*()-_=+" for c in p): charset += 15
        entropy = len(p) * math.log2(charset) if charset else 0
        if entropy < 28: level = "Çok Zayıf"
        elif entropy < 36: level = "Zayıf"
        elif entropy < 60: level = "Orta"
        elif entropy < 128: level = "Güçlü"
        else: level = "Çok Güçlü"
        return ok({"uzunluk": len(p), "charset": charset, "entropy_bits": round(entropy, 1), "seviye": level})
    except Exception as e: return err(f"PassStrength: {str(e)[:120]}")


@app.route("/api/jwt", methods=["POST"])
@login_required
def api_jwt():
    try:
        d = request.get_json(silent=True) or {}
        j = d.get("jwt", "").strip()[:5000]
        if not j: return err("JWT gerekli")
        parts = j.split(".")
        if len(parts) < 2: return err("Geçersiz JWT")
        result = {}
        for i, name in enumerate(["Header","Payload"]):
            pad = parts[i] + "=" * (-len(parts[i]) % 4)
            result[name] = json.loads(base64.urlsafe_b64decode(pad))
        return ok(result)
    except Exception as e: return err(f"JWT: {str(e)[:120]}")


@app.route("/api/hex", methods=["POST"])
@login_required
def api_hex():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        result = {"Hex Encode": t.encode().hex()}
        try: result["Hex Decode"] = bytes.fromhex(t).decode(errors="ignore")[:1000]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Hex: {str(e)[:120]}")


@app.route("/api/rot13", methods=["POST"])
@login_required
def api_rot13():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        try: n = int(d.get("shift", 13) or 13)
        except Exception: n = 13
        n = n % 26
        result = "".join(chr((ord(c) - (ord('A') if c.isupper() else ord('a')) + n) % 26 + (ord('A') if c.isupper() else ord('a'))) if c.isalpha() else c for c in t)
        return ok({"Sonuç": result})
    except Exception as e: return err(f"ROT13: {str(e)[:120]}")


@app.route("/api/binary", methods=["POST"])
@login_required
def api_binary():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        result = {"Binary Encode": " ".join(format(ord(c), "08b") for c in t)}
        try:
            bits = "".join(t.split())
            if len(bits) % 8 == 0 and all(c in "01" for c in bits):
                result["Binary Decode"] = "".join(chr(int(bits[i:i+8], 2)) for i in range(0, len(bits), 8))[:1000]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Binary: {str(e)[:120]}")


@app.route("/api/base32", methods=["POST"])
@login_required
def api_base32():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        result = {"Base32 Encode": base64.b32encode(t.encode()).decode()}
        try: result["Base32 Decode"] = base64.b32decode(t.encode()).decode(errors="ignore")[:1000]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Base32: {str(e)[:120]}")


@app.route("/api/urlencode", methods=["POST"])
@login_required
def api_urlencode():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        return ok({"Encode": urllib.parse.quote(t), "Decode": urllib.parse.unquote(t)})
    except Exception as e: return err(f"URLEncode: {str(e)[:120]}")


@app.route("/api/htmlentity", methods=["POST"])
@login_required
def api_htmlentity():
    try:
        import html
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        return ok({"Encode": html.escape(t), "Decode": html.unescape(t)})
    except Exception as e: return err(f"HTMLEntity: {str(e)[:120]}")


# ==================== EXTRA SAFE UTILITIES (100+) ====================
EXTRA_OPS = [('Uppercase', 'upper'), ('Lowercase', 'lower'), ('Title Case', 'title'), ('Swap Case', 'swapcase'), ('Trim', 'trim'), ('Reverse', 'reverse'), ('Line Count', 'linecount'), ('Char Count', 'charcount'), ('Word Count', 'wordcount'), ('Unique Lines', 'uniq'), ('Sorted Lines', 'sort'), ('Sort Reverse', 'sortrev'), ('CSV Parse', 'csv'), ('JSON Pretty', 'jsonpretty'), ('JSON Minify', 'jsonmin'), ('URL Encode', 'urlencode2'), ('URL Decode', 'urldecode2'), ('HTML Escape', 'htmlescape'), ('HTML Unescape', 'htmlunescape'), ('Unicode Normalize', 'nfkc'), ('Remove Accents', 'accents'), ('Digits Only', 'digits'), ('Letters Only', 'letters'), ('Alnum Only', 'alnum'), ('Whitespace Normalize', 'spaces'), ('Remove Blank Lines', 'noblank'), ('Add Line Numbers', 'linenum'), ('Slugify', 'slug'), ('Camel Case', 'camel'), ('Snake Case', 'snake'), ('Kebab Case', 'kebab'), ('Dot Case', 'dotcase'), ('Pascal Case', 'pascal'), ('Repeat 2x', 'repeat2'), ('Repeat 3x', 'repeat3'), ('ROT13', 'rot13x'), ('Binary Encode', 'binenc'), ('Hex Encode', 'hexenc'), ('Base64 Encode', 'b64enc'), ('Base64 Decode', 'b64dec'), ('Base32 Encode', 'b32enc'), ('Base32 Decode', 'b32dec'), ('ASCII Codes', 'asciicodes'), ('Codepoints', 'codepoints'), ('Char Frequencies', 'freq'), ('Most Common Char', 'commonchar'), ('Palindrome Check', 'palindrome'), ('Anagram Signature', 'anagram'), ('MD5', 'md5'), ('SHA1', 'sha1'), ('SHA256', 'sha256'), ('SHA512', 'sha512'), ('UUID', 'uuid'), ('Timestamp Now', 'nowts'), ('ISO Now', 'nowiso'), ('URL Parse', 'urlparse2'), ('Domain Extract', 'domain'), ('Path Extract', 'path'), ('Query Extract', 'query'), ('Fragment Extract', 'fragment'), ('Email Mask', 'emailmask'), ('IP Validate', 'ipvalid'), ('IPv4 Validate', 'ipv4'), ('IPv6 Validate', 'ipv6'), ('CIDR Validate', 'cidrvalid'), ('Port Validate', 'portvalid'), ('Hex Validate', 'hexvalid'), ('UUID Validate', 'uuidvalid'), ('JSON Validate', 'jsonvalid'), ('Regex Escape', 'regexescape'), ('HTML Tag Strip', 'striphtml'), ('Duplicate Chars', 'dupechars'), ('Unique Chars', 'uniquechars'), ('Sort Chars', 'sortchars'), ('Reverse Words', 'revwords'), ('First Word', 'firstword'), ('Last Word', 'lastword'), ('Initials', 'initials'), ('Line Lengths', 'linelengths'), ('Longest Line', 'longest'), ('Shortest Line', 'shortest'), ('Average Line Length', 'avgline'), ('Character Histogram', 'hist'), ('Tabs To Spaces', 'tabs'), ('Spaces To Tabs', 'spaces_tabs'), ('CRLF To LF', 'lf'), ('LF To CRLF', 'crlf'), ('Remove BOM', 'bom'), ('JSON Keys', 'jsonkeys'), ('JSON Values', 'jsonvalues'), ('CSV To JSON', 'csvjson'), ('JSON To CSV', 'jsoncsv'), ('HTML Text', 'htmltext'), ('Markdown Escape', 'mdescape'), ('Quote Escape', 'quoteescape'), ('Python String Escape', 'pyescape'), ('C String Escape', 'cescape'), ('URL Query Decode', 'querydecode'), ('URL Query Encode', 'queryencode'), ('Percent Decode', 'pctdecode'), ('Percent Encode', 'pctencode'), ('ROT47', 'rot47'), ('Atbash', 'atbash'), ('Caesar 3', 'caesar3'), ('Whitespace Visible', 'whitespace'), ('Text Statistics', 'stats'), ('Number Statistics', 'numstats')]


def _safe_ip_obj(v):
    try:
        return ipaddress.ip_address(v)
    except Exception:
        return None

def _safe_ip(v):
    return ipaddress.ip_address(v)

def _safe_ip_valid(v):
    try:
        ipaddress.ip_address(v)
        return True
    except Exception:
        return False

def _is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    r = int(math.isqrt(n))
    for i in range(3, r + 1, 2):
        if n % i == 0: return False
    return True


@app.route("/api/extra/<op>", methods=["POST"])
@login_required
@limiter.limit("120 per minute")
def api_extra(op):
    try:
        d=request.get_json(silent=True) or {}
        textv=str(d.get("text",""))[:50000]
        log_event("TOOL_RUN", f"tool={op}")
        import base64 as _b64, html as _html, uuid as _uuid, unicodedata as _ud, urllib.parse as _up, re as _re, json as _json, csv as _csv, io as _io, statistics as _statistics, difflib as _difflib
        lines=textv.splitlines()
        words=textv.split()
        if op=="upper": out=textv.upper()
        elif op=="lower": out=textv.lower()
        elif op=="title": out=textv.title()
        elif op=="swapcase": out=textv.swapcase()
        elif op=="trim": out=textv.strip()
        elif op=="reverse": out=textv[::-1]
        elif op=="linecount": out=len(lines)
        elif op=="charcount": out=len(textv)
        elif op=="wordcount": out=len(words)
        elif op=="uniq": out="\n".join(dict.fromkeys(lines))
        elif op=="sort": out="\n".join(sorted(lines,key=str.casefold))
        elif op=="sortrev": out="\n".join(sorted(lines,key=str.casefold,reverse=True))
        elif op=="csv": out=list(_csv.reader(_io.StringIO(textv)))
        elif op=="jsonpretty": out=_json.dumps(_json.loads(textv),ensure_ascii=False,indent=2)
        elif op=="jsonmin": out=_json.dumps(_json.loads(textv),ensure_ascii=False,separators=(",",":"))
        elif op=="urlencode2": out=_up.quote(textv,safe="")
        elif op in ("urldecode2","pctdecode"): out=_up.unquote(textv)
        elif op in ("pctencode","urlencode2"): out=_up.quote(textv,safe="")
        elif op=="htmlescape": out=_html.escape(textv)
        elif op=="htmlunescape": out=_html.unescape(textv)
        elif op=="nfkc": out=_ud.normalize("NFKC",textv)
        elif op=="accents": out="".join(c for c in _ud.normalize("NFKD",textv) if not _ud.combining(c))
        elif op=="digits": out="".join(c for c in textv if c.isdigit())
        elif op=="letters": out="".join(c for c in textv if c.isalpha())
        elif op=="alnum": out="".join(c for c in textv if c.isalnum())
        elif op=="spaces": out=" ".join(textv.split())
        elif op=="noblank": out="\n".join(x for x in lines if x.strip())
        elif op=="linenum": out="\n".join(f"{i+1}: {x}" for i,x in enumerate(lines))
        elif op=="slug": out=_re.sub(r"[^a-z0-9]+","-",textv.lower()).strip("-")
        elif op in ("camel","snake","kebab","dotcase","pascal"):
            w=[x for x in _re.split(r"[^A-Za-z0-9]+",textv) if x]
            if op=="snake": out="_".join(x.lower() for x in w)
            elif op=="kebab": out="-".join(x.lower() for x in w)
            elif op=="dotcase": out=".".join(x.lower() for x in w)
            elif op=="pascal": out="".join(x[:1].upper()+x[1:].lower() for x in w)
            else: out=(w[0].lower()+"".join(x[:1].upper()+x[1:].lower() for x in w[1:])) if w else ""
        elif op=="repeat2": out=textv*2
        elif op=="repeat3": out=textv*3
        elif op=="rot13x": import codecs; out=codecs.decode(textv,"rot_13")
        elif op=="binenc": out=" ".join(format(b,"08b") for b in textv.encode())
        elif op=="hexenc": out=textv.encode().hex()
        elif op=="b64enc": out=_b64.b64encode(textv.encode()).decode()
        elif op=="b64dec": out=_b64.b64decode(textv).decode("utf-8",errors="replace")
        elif op=="b32enc": out=_b64.b32encode(textv.encode()).decode()
        elif op=="b32dec": out=_b64.b32decode(textv).decode("utf-8",errors="replace")
        elif op=="asciicodes": out=[ord(c) for c in textv]
        elif op=="codepoints": out=[f"U+{ord(c):04X}" for c in textv]
        elif op=="freq": out={c:textv.count(c) for c in sorted(set(textv))}
        elif op=="commonchar": out=_statistics.mode(textv) if textv else ""
        elif op=="palindrome": out=(textv==textv[::-1])
        elif op=="anagram": out="".join(sorted(c.lower() for c in textv if not c.isspace()))
        elif op in ("md5","sha1","sha256","sha512"):
            import hashlib as _h; out=getattr(_h,op)(textv.encode()).hexdigest()
        elif op=="uuid": out=str(_uuid.uuid4())
        elif op=="nowts": out=int(time.time())
        elif op=="nowiso": out=datetime.now().isoformat()
        elif op.startswith("urlparse2"):
            q=_up.urlparse(textv); out={"scheme":q.scheme,"netloc":q.netloc,"path":q.path,"query":q.query,"fragment":q.fragment}
        elif op=="domain": out=_up.urlparse(textv if "://" in textv else "https://"+textv).hostname or ""
        elif op=="path": out=_up.urlparse(textv).path
        elif op=="query": out=_up.urlparse(textv).query
        elif op=="fragment": out=_up.urlparse(textv).fragment
        elif op=="emailmask": out=_re.sub(r"(^.).*(@.*$)",r"\1***\2",textv)
        elif op=="ipvalid":
            try: ipaddress.ip_address(textv); out=True
            except: out=False
        elif op=="ipv4":
            try: out=ipaddress.ip_address(textv).version==4
            except: out=False
        elif op=="ipv6":
            try: out=ipaddress.ip_address(textv).version==6
            except: out=False
        elif op=="cidrvalid":
            try: ipaddress.ip_network(textv,strict=False); out=True
            except: out=False
        elif op=="portvalid": out=textv.isdigit() and 1<=int(textv)<=65535
        elif op=="hexvalid": out=bool(_re.fullmatch(r"[0-9A-Fa-f]+",textv or ""))
        elif op=="uuidvalid": out=bool(_re.fullmatch(r"[0-9a-fA-F]{8}-[0-9a-fA-F]{4}-[1-5][0-9a-fA-F]{3}-[89abAB][0-9a-fA-F]{3}-[0-9a-fA-F]{12}",textv))
        elif op=="jsonvalid":
            try: _json.loads(textv); out=True
            except: out=False
        elif op=="regexescape": out=_re.escape(textv)
        elif op=="striphtml": out=_re.sub(r"<[^>]*>","",textv)
        elif op=="dupechars": out="".join(c for c in textv if textv.count(c)>1)
        elif op=="uniquechars": out="".join(dict.fromkeys(textv))
        elif op=="sortchars": out="".join(sorted(textv))
        elif op=="revwords": out=" ".join(words[::-1])
        elif op=="firstword": out=words[0] if words else ""
        elif op=="lastword": out=words[-1] if words else ""
        elif op=="initials": out="".join(x[0] for x in words if x)
        elif op=="linelengths": out=[len(x) for x in lines]
        elif op=="longest": out=max(lines,key=len) if lines else ""
        elif op=="shortest": out=min(lines,key=len) if lines else ""
        elif op=="avgline": out=(sum(map(len,lines))/len(lines)) if lines else 0
        elif op=="hist": out={str(i):textv.count(chr(i)) for i in range(32,127) if chr(i) in textv}
        elif op=="tabs": out=textv.replace("\t","    ")
        elif op=="spaces_tabs": out=textv.replace("    ","\t")
        elif op=="lf": out=textv.replace("\r\n","\n").replace("\r","\n")
        elif op=="crlf": out=textv.replace("\r\n","\n").replace("\r","\n").replace("\n","\r\n")
        elif op=="bom": out=textv.lstrip("\ufeff")
        elif op=="jsonkeys": out=list(_json.loads(textv).keys())
        elif op=="jsonvalues": out=list(_json.loads(textv).values())
        elif op=="csvjson": out=[dict(r) for r in _csv.DictReader(_io.StringIO(textv))]
        elif op=="jsoncsv":
            arr=_json.loads(textv); out="\n".join(_csv.DictWriter(_io.StringIO(),fieldnames=list(arr[0].keys())).fieldnames) if False else _csvjson_dump(arr)
        elif op=="htmltext": out=_html.unescape(_re.sub(r"<[^>]*>","",textv))
        elif op=="mdescape": out=_re.sub(r"([\\`*_{}\[\]()<>#+.!|~-])",r"\\\1",textv)
        elif op=="quoteescape": out=textv.replace(chr(92),chr(92)+chr(92)).replace(chr(34),chr(92)+chr(34))
        elif op in ("pyescape","cescape"): out=textv.encode("unicode_escape").decode()
        elif op in ("querydecode","urldecode2"): out=_up.unquote_plus(textv)
        elif op=="queryencode": out=_up.quote_plus(textv)
        elif op=="rot47": out="".join(chr(33+(ord(c)-33+47)%94) if 33<=ord(c)<=126 else c for c in textv)
        elif op=="atbash": out="".join(chr(ord('Z')-(ord(c)-ord('A'))) if 'A'<=c<='Z' else chr(ord('z')-(ord(c)-ord('a'))) if 'a'<=c<='z' else c for c in textv)
        elif op=="caesar3": out="".join(chr(ord('A')+(ord(c)-65+3)%26) if 'A'<=c<='Z' else chr(ord('a')+(ord(c)-97+3)%26) if 'a'<=c<='z' else c for c in textv)
        elif op=="whitespace": out=textv.replace(" ","·").replace("\t","→").replace("\n","↵\n")
        elif op=="stats": out={"chars":len(textv),"words":len(words),"lines":len(lines),"digits":sum(c.isdigit() for c in textv),"letters":sum(c.isalpha() for c in textv)}
        elif op=="numstats":
            nums=[float(x) for x in _re.findall(r"-?\d+(?:\.\d+)?",textv)]; out={"count":len(nums),"sum":sum(nums),"min":min(nums) if nums else None,"max":max(nums) if nums else None,"mean":(_statistics.mean(nums) if nums else None)}

        elif op=="vowels": out=sum(c.lower() in 'aeiouöüıi' for c in textv)
        elif op=="consonants": out=sum(c.isalpha() and c.lower() not in 'aeiouöüıi' for c in textv)
        elif op=="digitsum": out=sum(int(c) for c in textv if c.isdigit())
        elif op=="asciisum": out=sum(ord(c) for c in textv)
        elif op=="unique_words": out=len(set(w.casefold() for w in words))
        elif op=="avgword": out=(sum(len(w) for w in words)/len(words)) if words else 0
        elif op=="longword": out=max(words, key=len) if words else ''
        elif op=="shortword": out=min(words, key=len) if words else ''
        elif op=="reverse_lines": out='\n'.join(lines[::-1])
        elif op=="reverse_each_line": out='\n'.join(x[::-1] for x in lines)
        elif op=="dedupe_words": out=' '.join(dict.fromkeys(words))
        elif op=="sort_words": out=' '.join(sorted(words, key=str.casefold))
        elif op=="sort_words_rev": out=' '.join(sorted(words, key=str.casefold, reverse=True))
        elif op=="lower_lines": out='\n'.join(x.lower() for x in lines)
        elif op=="upper_lines": out='\n'.join(x.upper() for x in lines)
        elif op=="title_lines": out='\n'.join(x.title() for x in lines)
        elif op=="trim_lines": out='\n'.join(x.strip() for x in lines)
        elif op=="remove_vowels": out=''.join(c for c in textv if c.lower() not in 'aeiouöüıi')
        elif op=="remove_digits": out=''.join(c for c in textv if not c.isdigit())
        elif op=="remove_letters": out=''.join(c for c in textv if not c.isalpha())
        elif op=="remove_punct": out=''.join(c for c in textv if c.isalnum() or c.isspace())
        elif op=="only_ascii": out=textv.encode('ascii', errors='ignore').decode()
        elif op=="ascii_codes_hex": out=' '.join(f'{ord(c):02x}' for c in textv)
        elif op=="unicode_names": out=[unicodedata.name(c, 'UNKNOWN') for c in textv]
        elif op=="unicode_escape": out=textv.encode('unicode_escape').decode()
        elif op=="json_string": out=json.dumps(textv, ensure_ascii=False)
        elif op=="json_unstring": out=json.loads(textv)
        elif op=="b64urlenc": out=base64.urlsafe_b64encode(textv.encode()).decode()
        elif op=="b64urldec": out=base64.urlsafe_b64decode(textv + '=' * (-len(textv)%4)).decode('utf-8', errors='replace')
        elif op=="b85enc": out=base64.b85encode(textv.encode()).decode()
        elif op=="b85dec": out=base64.b85decode(textv).decode('utf-8', errors='replace')
        elif op=="a85enc": out=base64.a85encode(textv.encode()).decode()
        elif op=="a85dec": out=base64.a85decode(textv).decode('utf-8', errors='replace')
        elif op=="hexdec": out=bytes.fromhex(re.sub(r'\s+', '', textv)).decode('utf-8', errors='replace')
        elif op=="bindec": out=bytes(int(x,2) for x in textv.split()).decode('utf-8', errors='replace')
        elif op=="octenc": out=' '.join(format(b, '03o') for b in textv.encode())
        elif op=="octdec": out=bytes(int(x,8) for x in textv.split()).decode('utf-8', errors='replace')
        elif op=="decimalenc": out=' '.join(str(b) for b in textv.encode())
        elif op=="decimaldec": out=bytes(int(x) for x in textv.split()).decode('utf-8', errors='replace')
        elif op=="sha224": out=hashlib.sha224(textv.encode()).hexdigest()
        elif op=="sha384": out=hashlib.sha384(textv.encode()).hexdigest()
        elif op=="sha3_256": out=hashlib.sha3_256(textv.encode()).hexdigest()
        elif op=="sha3_512": out=hashlib.sha3_512(textv.encode()).hexdigest()
        elif op=="blake2b": out=hashlib.blake2b(textv.encode()).hexdigest()
        elif op=="blake2s": out=hashlib.blake2s(textv.encode()).hexdigest()
        elif op=="token32": out=secrets.token_hex(16)
        elif op=="token64": out=secrets.token_hex(32)
        elif op=="url_safe_token": out=secrets.token_urlsafe(32)
        elif op=="uuid_hex": out=uuid.uuid4().hex
        elif op=="uuid_int": out=uuid.uuid4().int
        elif op=="timestamp_ms": out=int(time.time()*1000)
        elif op=="utc_iso": out=datetime.now(timezone.utc).isoformat()
        elif op=="utc_date": out=datetime.now(timezone.utc).strftime('%Y-%m-%d')
        elif op=="utc_time": out=datetime.now(timezone.utc).strftime('%H:%M:%S')
        elif op=="weekday": out=datetime.now().strftime('%A')
        elif op=="week": out=datetime.now().isocalendar().week
        elif op=="year": out=datetime.now().year
        elif op=="month": out=datetime.now().month
        elif op=="day": out=datetime.now().day
        elif op=="hour": out=datetime.now().hour
        elif op=="minute": out=datetime.now().minute
        elif op=="second": out=datetime.now().second
        elif op=="ip_valid": out=bool(re.fullmatch(r'[0-9a-fA-F:.]+', textv)) and _safe_ip_valid(textv)
        elif op=="ipv4_private": out=(_safe_ip(textv).version == 4 and _safe_ip(textv).is_private) if _safe_ip_obj(textv) else False
        elif op=="ipv4_public": out=(_safe_ip(textv).version == 4 and _safe_ip(textv).is_global) if _safe_ip_obj(textv) else False
        elif op=="ipv6_private": out=(_safe_ip(textv).version == 6 and _safe_ip(textv).is_private) if _safe_ip_obj(textv) else False
        elif op=="loopback": out=_safe_ip_obj(textv).is_loopback if _safe_ip_obj(textv) else False
        elif op=="multicast": out=_safe_ip_obj(textv).is_multicast if _safe_ip_obj(textv) else False
        elif op=="port_valid": out=textv.isdigit() and 1 <= int(textv) <= 65535
        elif op=="discord_id_valid": out=textv.isdigit() and 17 <= len(textv) <= 20
        elif op=="discord_created": out=datetime.fromtimestamp(((int(textv)>>22)+1420070400000)/1000).strftime('%Y-%m-%d %H:%M:%S') if textv.isdigit() else 'Geçersiz'
        elif op=="discord_default_avatar": out=f'https://cdn.discordapp.com/embed/avatars/{(int(textv)>>22)%6}.png' if textv.isdigit() else ''
        elif op=="email_valid": out=bool(re.fullmatch(r'[^\s@]+@[^\s@]+\.[^\s@]+', textv))
        elif op=="url_valid": out=bool(urllib.parse.urlparse(textv).scheme in ('http','https') and urllib.parse.urlparse(textv).hostname)
        elif op=="domain_extract": out=urllib.parse.urlparse(textv if '://' in textv else 'https://'+textv).hostname or ''
        elif op=="query_params": out=dict(urllib.parse.parse_qsl(urllib.parse.urlparse(textv).query, keep_blank_values=True))
        elif op=="fragment_extract": out=urllib.parse.urlparse(textv).fragment
        elif op=="path_extract": out=urllib.parse.urlparse(textv).path
        elif op=="scheme_extract": out=urllib.parse.urlparse(textv).scheme
        elif op=="hostname_valid": out=bool(re.fullmatch(r'[A-Za-z0-9.-]{1,253}', textv))
        elif op=="slug_strict": out=re.sub(r'[^a-z0-9]+','-',textv.casefold()).strip('-')
        elif op=="snake_strict": out=re.sub(r'[^a-zA-Z0-9]+','_',textv).strip('_').lower()
        elif op=="kebab_strict": out=re.sub(r'[^a-zA-Z0-9]+','-',textv).strip('-').lower()
        elif op=="dot_strict": out=re.sub(r'[^a-zA-Z0-9]+','.',textv).strip('.').lower()
        elif op=="collapse_newlines": out=re.sub(r'\n{3,}', '\n\n', textv)
        elif op=="collapse_spaces": out=re.sub(r'[ \t]+', ' ', textv)
        elif op=="remove_blank_lines": out='\n'.join(x for x in lines if x.strip())
        elif op=="pad_left": out=textv.rjust(max(len(textv), 20), '0')
        elif op=="pad_right": out=textv.ljust(max(len(textv), 20), '0')
        elif op=="center20": out=textv.center(20)
        elif op=="zfill20": out=textv.zfill(20)
        elif op=="repeat5": out=textv * 5
        elif op=="repeat10": out=textv * 10
        elif op=="char_frequency": out=dict(sorted({c:textv.count(c) for c in set(textv)}.items(), key=lambda x:(-x[1],x[0])))
        elif op=="word_frequency": out=dict(sorted({w:words.count(w) for w in set(words)}.items(), key=lambda x:(-x[1],x[0])))
        elif op=="number_list": out=[float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)]
        elif op=="number_sum": out=sum(float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv))
        elif op=="number_median": out=statistics.median([float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)]) if re.findall(r'-?\d+(?:\.\d+)?', textv) else None
        elif op=="number_stdev": out=statistics.stdev([float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)]) if len(re.findall(r'-?\d+(?:\.\d+)?', textv))>1 else 0
        elif op=="number_variance": out=statistics.variance([float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)]) if len(re.findall(r'-?\d+(?:\.\d+)?', textv))>1 else 0
        elif op=="number_range": out=(max([float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)])-min([float(x) for x in re.findall(r'-?\d+(?:\.\d+)?', textv)])) if re.findall(r'-?\d+(?:\.\d+)?', textv) else 0
        elif op=="is_even": out=int(textv)%2==0 if textv.lstrip('-').isdigit() else False
        elif op=="is_odd": out=int(textv)%2!=0 if textv.lstrip('-').isdigit() else False
        elif op=="is_prime": out=(_is_prime(int(textv))) if textv.lstrip('-').isdigit() else False
        elif op=="factorial": out=math.factorial(int(textv)) if textv.isdigit() and int(textv)<=1000 else '0-1000 arası tam sayı gerekli'
        elif op=="gcd_pair": out=math.gcd(*[int(x) for x in re.findall(r'-?\d+', textv)[:2]]) if len(re.findall(r'-?\d+', textv))>=2 else None
        elif op=="lcm_pair": out=math.lcm(*[int(x) for x in re.findall(r'-?\d+', textv)[:2]]) if len(re.findall(r'-?\d+', textv))>=2 else None
        elif op=="percent_of": out=({'a':float(re.findall(r'-?\d+(?:\.\d+)?',textv)[0]),'b':float(re.findall(r'-?\d+(?:\.\d+)?',textv)[1]),'result':float(re.findall(r'-?\d+(?:\.\d+)?',textv)[0])*float(re.findall(r'-?\d+(?:\.\d+)?',textv)[1])/100} if len(re.findall(r'-?\d+(?:\.\d+)?',textv))>=2 else None)
        elif op=="regex_escape2": out=re.escape(textv)
        elif op=="strip_tags2": out=re.sub(r'<[^>]+>', '', textv)
        elif op=="html_escape2": out=html.escape(textv)
        elif op=="html_unescape2": out=html.unescape(textv)
        elif op=="nfkd": out=unicodedata.normalize('NFKD', textv)
        elif op=="nfc": out=unicodedata.normalize('NFC', textv)
        elif op=="casefold": out=textv.casefold()
        elif op=="capitalize": out=textv.capitalize()
        elif op=="swapcase2": out=textv.swapcase()
        elif op=="reverse_words": out=' '.join(words[::-1])
        elif op=="first_line": out=lines[0] if lines else ''
        elif op=="last_line": out=lines[-1] if lines else ''
        elif op=="linecount_nonempty": out=sum(bool(x.strip()) for x in lines)
        elif op=="byte_count_utf8": out=len(textv.encode('utf-8'))
        elif op=="byte_count_ascii": out=len(textv.encode('ascii',errors='ignore'))
        elif op=="entropy": out=(-sum((n/len(textv))*math.log2(n/len(textv)) for n in [textv.count(c) for c in set(textv)]) if textv else 0)
        elif op=="palindrome_clean": out=re.sub(r'[^a-z0-9]','',textv.casefold()) == re.sub(r'[^a-z0-9]','',textv.casefold())[::-1]
        elif op=="anagram_signature": out=''.join(sorted(c for c in textv.casefold() if c.isalnum()))
        elif op=="random_hex16": out=secrets.token_hex(8)
        elif op=="random_hex32": out=secrets.token_hex(16)
        elif op=="random_url_token": out=secrets.token_urlsafe(16)
        elif op=="random_uuid": out=str(uuid.uuid4())
        elif op=="random_uuid_hex": out=uuid.uuid4().hex
        elif op=="random_bytes16": out=base64.b64encode(secrets.token_bytes(16)).decode()
        else: return err("Bilinmeyen araç",404)
        return ok({"input":textv,"result":out})
    except Exception as e:
        return err(f"Extra: {str(e)[:150]}")

def _csvjson_dump(arr):
    if not arr: return ""
    out=_io.StringIO(); w=_csv.DictWriter(out,fieldnames=list(arr[0].keys())); w.writeheader(); w.writerows(arr); return out.getvalue()


# ==================== RECON ====================
@app.route("/api/whois", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_whois():
    try:
        d = request.get_json(silent=True) or {}
        dom = d.get("domain", "").strip()
        if not dom or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', dom): return err("Geçersiz domain")
        if not HAS_WHOIS: return err("python-whois yok")
        w = whois.whois(dom)
        return ok({k: str(v)[:500] for k, v in dict(w).items()})
    except Exception as e: return err(f"Whois: {str(e)[:120]}")


@app.route("/api/urlparse", methods=["POST"])
@login_required
def api_urlparse():
    try:
        d = request.get_json(silent=True) or {}
        p = urllib.parse.urlparse(d.get("url","").strip()[:2000])
        return ok({"Scheme": p.scheme, "Host": p.netloc, "Path": p.path, "Query": p.query, "Fragment": p.fragment})
    except Exception as e: return err(f"URL parse: {str(e)[:120]}")


@app.route("/api/wayback", methods=["POST"])
@login_required
def api_wayback():
    try:
        d = request.get_json(silent=True) or {}
        url = d.get("url","").strip()[:500]
        if not url: return err("URL gerekli")
        r = safe_get("http://archive.org/wayback/available", params={"url": url}, allow_http=True)
        s = r.json().get("archived_snapshots", {}).get("closest")
        return ok({"Snapshot": s["timestamp"], "URL": s["url"]}) if s else err("Snapshot yok")
    except Exception as e: return err(f"Wayback: {str(e)[:120]}")


@app.route("/api/discord", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_discord():
    try:
        d = request.get_json(silent=True) or {}
        uname = str(d.get("username", "")).strip().lstrip("@")[:50]
        if not uname or not re.match(r'^[a-zA-Z0-9_.-]+$', uname):
            return err("Geçersiz username")
        return ok({
            "username": uname,
            "Durum": "Discord API kullanılmıyor",
            "not": "Bu sürüm bot/token/OAuth kullanmadan yalnızca yerel format kontrolü yapar."
        })
    except Exception as e:
        return err(f"Discord: {str(e)[:120]}")


def _discord_asset_url(user_id, asset_hash, kind="avatar", size=512):
    # Asset URL üretmek token gerektirmez, ancak gerçek hash bilinmiyorsa kullanılmaz.
    if not asset_hash:
        return None
    ext = "gif" if str(asset_hash).startswith("a_") else "png"
    return f"https://cdn.discordapp.com/{kind}s/{user_id}/{asset_hash}.{ext}?size={size}"

def _discord_default_avatar(user_id):
    try:
        return f"https://cdn.discordapp.com/embed/avatars/{(int(user_id) >> 22) % 6}.png"
    except Exception:
        return "https://cdn.discordapp.com/embed/avatars/0.png"

@app.route("/api/discordid", methods=["POST"])
@login_required
@limiter.limit("15 per minute")
def api_discordid():
    try:
        d = request.get_json(silent=True) or {}
        uid = str(d.get("id", "")).strip()
        if not uid.isdigit() or not 17 <= len(uid) <= 20:
            return err("Geçerli Discord ID gerekli (17-20 hane)")

        # Tokenless mode: only deterministic Snowflake facts are returned.
        snowflake = int(uid)
        created_ms = (snowflake >> 22) + 1420070400000
        created_dt = datetime.fromtimestamp(created_ms / 1000)
        default_avatar = _discord_default_avatar(uid)
        result = {
            "id": uid,
            "profil_url": f"https://discord.com/users/{uid}",
            "oluşturulma": created_dt.strftime("%Y-%m-%d %H:%M:%S"),
            "hesap_yaşı": f"{max(0, (datetime.now() - created_dt).days)} gün",
            "_avatar": default_avatar,
            "_banner": None,
            "avatar_durumu": "Bot token yok; yalnızca varsayılan avatar gösteriliyor",
            "banner_durumu": "Bot token/OAuth2 olmadan gerçek banner alınamıyor",
            "bio": "OAuth2 ile kullanıcı yetkilendirmesi gerekir",
            "hitaplar": "OAuth2 ile kullanıcı yetkilendirmesi gerekir",
            "bağlı_hesaplar": "OAuth2 + connections kapsamı gerekir",
            "not": "Bu sonuç yalnızca Discord ID/Snowflake hesabından hesaplanmıştır; API ile profil verisi çekilmez.",
        }
        result["Hesap Bilgileri"] = {
            "ID": uid,
            "Oluşturulma": result["oluşturulma"],
            "Hesap Yaşı": result["hesap_yaşı"],
            "Gerçek Avatar": "Bot token gerekli",
            "Banner": "Bot token/OAuth2 gerekli",
            "Bio": "Yetkilendirme gerekli",
            "Hitaplar": "Yetkilendirme gerekli",
            "Bağlı Hesaplar": "Yetkilendirme gerekli",
            "Email (DEMO)": "Kullanıcıya ait değil",
            "Telefon (DEMO)": "Kullanıcıya ait değil",
            "Not": "Gerçek e-posta/telefon yerine demo alanları kullanılmalıdır.",
        }
        return ok(result)
    except Exception as e:
        return err(f"DiscordID: {str(e)[:150]}")

@app.route("/api/github", methods=["POST"])
@login_required
def api_github():
    try:
        d = request.get_json(silent=True) or {}
        uname = d.get("username","").strip()[:50]
        if not re.match(r'^[a-zA-Z0-9-]+$', uname): return err("Geçersiz")
        r = safe_get(f"https://api.github.com/users/{uname}")
        if r.status_code != 200: return err("Bulunamadı")
        x = r.json()
        return ok({"login": x.get("login"), "name": x.get("name"), "bio": x.get("bio"),
                   "repos": x.get("public_repos"), "followers": x.get("followers"),
                   "url": x.get("html_url"), "_avatar": x.get("avatar_url")})
    except Exception as e: return err(f"GitHub: {str(e)[:120]}")


@app.route("/api/reddit", methods=["POST"])
@login_required
def api_reddit():
    try:
        d = request.get_json(silent=True) or {}
        uname = d.get("username","").strip()[:50]
        if not re.match(r'^[a-zA-Z0-9_-]+$', uname): return err("Geçersiz")
        r = safe_get(f"https://www.reddit.com/user/{uname}/about.json")
        if r.status_code != 200: return err("Bulunamadı")
        x = r.json().get("data", {})
        if not x.get("name"): return err("Bulunamadı")
        return ok({"name": x.get("name"), "karma": x.get("total_karma"),
                   "link_karma": x.get("link_karma"), "comment_karma": x.get("comment_karma"),
                   "_avatar": x.get("icon_img", "")})
    except Exception as e: return err(f"Reddit: {str(e)[:120]}")


@app.route("/api/zonetr", methods=["POST"])
@login_required
@limiter.limit("3 per minute")
def api_zonetr():
    try:
        d = request.get_json(silent=True) or {}
        dom = d.get("domain","").strip()
        if not dom or not re.match(r'^[a-zA-Z0-9.-]{1,253}$', dom): return err("Geçersiz")
        if not HAS_DNS: return err("dnspython yok")
        ns = [str(a) for a in dns.resolver.resolve(dom, "NS", lifetime=5)]
        results = []
        for n in ns:
            try:
                ip = socket.gethostbyname(n.rstrip("."))
                import dns.zone, dns.query
                dns.zone.from_xfr(dns.query.xfr(ip, dom, timeout=5))
                results.append({"NS": n, "Durum": "BAŞARILI"})
            except Exception: results.append({"NS": n, "Durum": "başarısız"})
        return ok(results)
    except Exception as e: return err(f"ZoneTransfer: {str(e)[:120]}")


# ==================== MISC ====================
@app.route("/api/qr", methods=["POST"])
@login_required
def api_qr():
    try:
        d = request.get_json(silent=True) or {}
        data = d.get("data","")[:2000]
        return ok({"URL": f"https://api.qrserver.com/v1/create-qr-code/?size=300x300&data={urllib.parse.quote(data)}"})
    except Exception as e: return err(f"QR: {str(e)[:120]}")


@app.route("/api/short", methods=["POST"])
@login_required
@limiter.limit("10 per minute")
def api_short():
    try:
        d = request.get_json(silent=True) or {}
        u = d.get("url","").strip()[:2000]
        if not u.startswith(("http://","https://")): return err("URL gerekli")
        ok_, msg = validate_url(u, allow_http=True)
        if not ok_: return err(msg)
        r = requests.head(u, allow_redirects=True, timeout=TIMEOUT, verify=True, headers=HEADERS)
        return ok({"Final URL": r.url})
    except Exception as e: return err(f"Short: {str(e)[:120]}")


@app.route("/api/urlshort", methods=["POST"])
@login_required
def api_urlshort():
    try:
        d = request.get_json(silent=True) or {}
        u = d.get("url","").strip()[:2000]
        if not u.startswith(("http://","https://")): return err("URL gerekli")
        r = safe_get(f"https://is.gd/create.php?format=simple&url={urllib.parse.quote(u)}")
        return ok({"Kısa URL": r.text.strip()[:200]})
    except Exception as e: return err(f"URLShort: {str(e)[:120]}")


@app.route("/api/uuid", methods=["POST"])
@login_required
def api_uuid():
    try:
        import uuid
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 5) or 5)
        except Exception: n = 5
        n = max(1, min(n, 100))
        return ok([str(uuid.uuid4()) for _ in range(n)])
    except Exception as e: return err(f"UUID: {str(e)[:120]}")


@app.route("/api/sysinfo", methods=["POST"])
@login_required
def api_sysinfo():
    try:
        return ok({"Python": sys.version.split()[0], "Platform": sys.platform, "Hostname": socket.gethostname()})
    except Exception as e: return err(f"Sysinfo: {str(e)[:120]}")


@app.route("/api/myip", methods=["POST"])
@login_required
def api_myip():
    try:
        r = safe_get("http://ip-api.com/json/?lang=tr", allow_http=True)
        return ok(r.json())
    except Exception as e: return err(f"MyIP: {str(e)[:120]}")


@app.route("/api/jsonfmt", methods=["POST"])
@login_required
def api_jsonfmt():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:100000]
        return ok({"_code": json.dumps(json.loads(t), indent=2, ensure_ascii=False)})
    except json.JSONDecodeError as e: return err(f"Geçersiz JSON: {str(e)[:120]}")
    except Exception as e: return err(f"JSON: {str(e)[:120]}")


@app.route("/api/diff", methods=["POST"])
@login_required
def api_diff():
    try:
        import difflib
        d = request.get_json(silent=True) or {}
        a = d.get("a","")[:50000].splitlines()
        b = d.get("b","")[:50000].splitlines()
        result = list(difflib.unified_diff(a, b, lineterm="", fromfile="1", tofile="2"))
        return ok({"_code": "\n".join(result)[:5000] if result else "(fark yok)"})
    except Exception as e: return err(f"Diff: {str(e)[:120]}")


@app.route("/api/useragent", methods=["POST"])
@login_required
def api_useragent():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 10) or 10)
        except Exception: n = 10
        n = max(1, min(n, 50))
        UAS = ["Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0",
               "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 Version/17.1",
               "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/119.0.0.0",
               "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15",
               "Mozilla/5.0 (Linux; Android 13) AppleWebKit/537.36 Chrome/119.0.0.0 Mobile"]
        return ok([secrets.choice(UAS) for _ in range(n)])
    except Exception as e: return err(f"UA: {str(e)[:120]}")


TR_NAMES = ["Ahmet","Mehmet","Mustafa","Ali","Hüseyin","Hasan","İbrahim","Osman","Yusuf","Murat",
            "Ömer","Ramazan","Halil","İsmail","Süleyman","Abdullah","Mahmut","Recep","Salih","Bekir",
            "Ayşe","Fatma","Emine","Hatice","Zeynep","Elif","Meryem","Şerife","Zehra","Sultan"]
TR_SURNAMES = ["Yılmaz","Kaya","Demir","Şahin","Çelik","Yıldız","Yıldırım","Öztürk","Aydın","Özdemir",
               "Arslan","Doğan","Kılıç","Aslan","Çetin","Kara","Koç","Kurt","Özkan","Şimşek"]
TR_CITIES = ["İstanbul","Ankara","İzmir","Bursa","Antalya","Adana","Konya","Gaziantep","Şanlıurfa","Mersin",
             "Diyarbakır","Kayseri","Eskişehir","Samsun","Denizli","Malatya","Kahramanmaraş","Erzurum","Van","Batman"]
TR_OPERATORS = {
    "Turkcell": ["530","531","532","533","534","535","536","537","538","539","561"],
    "Vodafone": ["540","541","542","543","544","545","546","547","548","549","551"],
    "Türk Telekom": ["500","501","502","503","504","505","506","507","508","509","552","553","554","555"],
}
TR_IP_BLOCKS = ["78.180.","78.181.","78.182.","78.183.","78.184.","85.96.","85.97.","85.98.","85.99.",
                "88.224.","88.225.","88.226.","88.227.","88.228.","94.54.","94.55.","94.56.","94.57.",
                "176.232.","176.233.","176.234.","185.125.","185.126.","212.156.","212.157.","213.153.","213.154."]


@app.route("/api/fakenum", methods=["POST"])
@login_required
def api_fakenum():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 5) or 5)
        except Exception: n = 5
        n = max(1, min(n, 50))
        operator = d.get("operator", "").strip().lower()
        results = []
        for _ in range(n):
            op = next((k for k in TR_OPERATORS if operator and operator in k.lower()), None)
            if not op: op = secrets.choice(list(TR_OPERATORS.keys()))
            prefix = secrets.choice(TR_OPERATORS[op])
            rest = "".join(secrets.choice(string.digits) for _ in range(7))
            num = f"+90 {prefix} {rest[:3]} {rest[3:5]} {rest[5:]}"
            results.append({"numara": num, "operatör": op, "isim": f"{secrets.choice(TR_NAMES)} {secrets.choice(TR_SURNAMES)}", "şehir": secrets.choice(TR_CITIES)})
        return ok(results)
    except Exception as e: return err(f"FakeNum: {str(e)[:120]}")


@app.route("/api/fakeip", methods=["POST"])
@login_required
def api_fakeip():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 5) or 5)
        except Exception: n = 5
        n = max(1, min(n, 50))
        results = []
        for _ in range(n):
            block = secrets.choice(TR_IP_BLOCKS)
            ip = f"{block}{secrets.randbelow(254)+1}.{secrets.randbelow(254)+1}"
            results.append({"ip": ip, "ülke": "Türkiye", "şehir": secrets.choice(TR_CITIES), "isp": secrets.choice(["Türk Telekom","Turkcell Superonline","Vodafone Net","TurkNet"])})
        return ok(results)
    except Exception as e: return err(f"FakeIP: {str(e)[:120]}")


@app.route("/api/fakecard", methods=["POST"])
@login_required
def api_fakecard():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 3) or 3)
        except Exception: n = 3
        n = max(1, min(n, 20))
        brands = {"Visa": "4", "Mastercard": "5", "Amex": "37", "Troy": "9"}
        results = []
        for _ in range(n):
            brand = secrets.choice(list(brands.keys()))
            prefix = brands[brand]
            length = 16 if brand != "Amex" else 15
            number = prefix + "".join(secrets.choice(string.digits) for _ in range(length - len(prefix) - 1))
            digits = [int(c) for c in number]
            for i in range(len(digits) - 1, -1, -1):
                if (len(digits) - i) % 2 == 1:
                    x = digits[i] * 2
                    if x > 9: x -= 9
                    digits[i] = x
            check = (10 - sum(digits) % 10) % 10
            number = number + str(check)
            formatted = " ".join(number[i:i+4] for i in range(0, len(number), 4))
            results.append({"kart_no": formatted, "marka": brand,
                            "son_kullanma": f"{secrets.randbelow(12)+1:02d}/{secrets.randbelow(5)+25}",
                            "cvv": f"{secrets.randbelow(900)+100}",
                            "sahip": f"{secrets.choice(TR_NAMES)} {secrets.choice(TR_SURNAMES)}"})
        return ok(results)
    except Exception as e: return err(f"FakeCard: {str(e)[:120]}")


@app.route("/api/faketc", methods=["POST"])
@login_required
def api_faketc():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 3) or 3)
        except Exception: n = 3
        n = max(1, min(n, 20))
        results = []
        for _ in range(n):
            tc = str(secrets.randbelow(9) + 1) + "".join(secrets.choice(string.digits) for _ in range(8))
            total = sum(int(tc[i]) for i in range(0, 9, 2)) * 7 - sum(int(tc[i]) for i in range(1, 9, 2))
            tc = tc + str(total % 10)
            tc = tc + str(sum(int(tc[i]) for i in range(0, 10)) % 10)
            results.append({"tc_no": tc, "ad": secrets.choice(TR_NAMES), "soyad": secrets.choice(TR_SURNAMES),
                            "doğum_yılı": secrets.randbelow(40) + 1960, "şehir": secrets.choice(TR_CITIES)})
        return ok(results)
    except Exception as e: return err(f"FakeTC: {str(e)[:120]}")


@app.route("/api/emailgen", methods=["POST"])
@login_required
def api_emailgen():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 5) or 5)
        except Exception: n = 5
        n = max(1, min(n, 50))
        domains = ["gmail.com","outlook.com","hotmail.com","yahoo.com","yandex.com","protonmail.com"]
        results = []
        for _ in range(n):
            ad = secrets.choice(TR_NAMES).lower()
            soyad = secrets.choice(TR_SURNAMES).lower()
            sayi = secrets.randbelow(999) + 1
            dom = secrets.choice(domains)
            results.append({"email": f"{ad}.{soyad}{sayi}@{dom}", "ad": ad.capitalize(), "soyad": soyad.capitalize(), "domain": dom})
        return ok(results)
    except Exception as e: return err(f"EmailGen: {str(e)[:120]}")


@app.route("/api/luhn", methods=["POST"])
@login_required
def api_luhn():
    try:
        d = request.get_json(silent=True) or {}
        n = re.sub(r'[^0-9]', '', d.get("number",""))
        if not n: return err("Rakam gerekli")
        digits = [int(c) for c in n]
        checksum = 0
        for i, x in enumerate(reversed(digits)):
            if i % 2 == 1:
                x *= 2
                if x > 9: x -= 9
            checksum += x
        return ok({"Geçerli": checksum % 10 == 0})
    except Exception as e: return err(f"Luhn: {str(e)[:120]}")


@app.route("/api/ipport", methods=["POST"])
@login_required
def api_ipport():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","").strip()[:100]
        if ":" not in t: return err("Format: IP:PORT")
        ip, port = t.rsplit(":", 1)
        result = {"IP": ip, "Port": port}
        try: result["Hostname"] = socket.gethostbyaddr(ip)[0]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"IPPort: {str(e)[:120]}")


@app.route("/api/lorem", methods=["POST"])
@login_required
def api_lorem():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("count", 3) or 3)
        except Exception: n = 3
        n = max(1, min(n, 20))
        words = "lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod tempor incididunt ut labore et dolore magna aliqua".split()
        return ok([" ".join(secrets.choice(words) for _ in range(50)).capitalize() + "." for _ in range(n)])
    except Exception as e: return err(f"Lorem: {str(e)[:120]}")


@app.route("/api/randstr", methods=["POST"])
@login_required
def api_randstr():
    try:
        d = request.get_json(silent=True) or {}
        try: n = int(d.get("length", 32) or 32)
        except Exception: n = 32
        try: c = int(d.get("count", 5) or 5)
        except Exception: c = 5
        n = max(1, min(n, 256)); c = max(1, min(c, 50))
        return ok([''.join(secrets.choice(string.ascii_letters + string.digits) for _ in range(n)) for _ in range(c)])
    except Exception as e: return err(f"RandStr: {str(e)[:120]}")


@app.route("/api/timestamp", methods=["POST"])
@login_required
def api_timestamp():
    try:
        d = request.get_json(silent=True) or {}
        ts = d.get("ts", "").strip()
        if ts:
            try:
                dt = datetime.fromtimestamp(int(ts))
            except Exception:
                dt = datetime.fromisoformat(ts)
        else: dt = datetime.now()
        return ok({"unix": int(dt.timestamp()), "iso": dt.isoformat(), "readable": dt.strftime("%Y-%m-%d %H:%M:%S"), "weekday": dt.strftime("%A")})
    except Exception as e: return err(f"Timestamp: {str(e)[:120]}")


@app.route("/api/mime", methods=["POST"])
@login_required
def api_mime():
    try:
        import mimetypes
        d = request.get_json(silent=True) or {}
        ext = d.get("ext","").strip().lower().lstrip(".")
        if not ext: return err("Uzantı gerekli")
        m = mimetypes.guess_type(f"x.{ext}")[0]
        return ok({"uzantı": ext, "mime": m or "bilinmiyor"})
    except Exception as e: return err(f"MIME: {str(e)[:120]}")


HTTP_STATUS = {200:"OK",201:"Created",204:"No Content",301:"Moved Permanently",302:"Found",304:"Not Modified",
    400:"Bad Request",401:"Unauthorized",403:"Forbidden",404:"Not Found",405:"Method Not Allowed",
    408:"Request Timeout",409:"Conflict",410:"Gone",418:"I'm a teapot",429:"Too Many Requests",
    500:"Internal Server Error",501:"Not Implemented",502:"Bad Gateway",503:"Service Unavailable",504:"Gateway Timeout"}

@app.route("/api/httpstatus", methods=["POST"])
@login_required
def api_httpstatus():
    try:
        d = request.get_json(silent=True) or {}
        code = d.get("code","").strip()
        if code:
            try: c = int(code)
            except Exception: return err("Geçersiz kod")
            return ok({str(c): HTTP_STATUS.get(c, "Bilinmeyen")})
        return ok(HTTP_STATUS)
    except Exception as e: return err(f"HTTPStatus: {str(e)[:120]}")


@app.route("/api/chmod", methods=["POST"])
@login_required
def api_chmod():
    try:
        d = request.get_json(silent=True) or {}
        perm = d.get("perm","").strip()
        if not re.match(r'^[0-7]{3}$', perm): return err("3 haneli octal (örn 755)")
        result = []
        for i, digit in enumerate(perm):
            n = int(digit)
            who = ["Sahip","Grup","Diğer"][i]
            result.append(f"{who}: {'r' if n&4 else '-'}{'w' if n&2 else '-'}{'x' if n&1 else '-'}")
        return ok({"perm": perm, "detay": result})
    except Exception as e: return err(f"Chmod: {str(e)[:120]}")


PORT_INFO = {20:"FTP-DATA",21:"FTP",22:"SSH",23:"Telnet",25:"SMTP",53:"DNS",67:"DHCP",68:"DHCP",80:"HTTP",110:"POP3",123:"NTP",143:"IMAP",161:"SNMP",389:"LDAP",443:"HTTPS",445:"SMB",465:"SMTPS",587:"SMTP",636:"LDAPS",993:"IMAPS",995:"POP3S",1433:"MSSQL",1521:"Oracle",3306:"MySQL",3389:"RDP",5432:"PostgreSQL",5900:"VNC",6379:"Redis",8080:"HTTP-Alt",8443:"HTTPS-Alt",27017:"MongoDB"}

@app.route("/api/portinfo", methods=["POST"])
@login_required
def api_portinfo():
    try:
        d = request.get_json(silent=True) or {}
        p = d.get("port","").strip()
        if not p.isdigit(): return err("Port gerekli")
        p = int(p)
        try: svc = socket.getservbyport(p, "tcp")
        except Exception: svc = PORT_INFO.get(p, "bilinmiyor")
        return ok({"port": p, "service": svc})
    except Exception as e: return err(f"PortInfo: {str(e)[:120]}")


@app.route("/api/base58", methods=["POST"])
@login_required
def api_base58():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
        def enc(b):
            n = int.from_bytes(b, "big"); s = ""
            while n > 0: n, r = divmod(n, 58); s = ALPHABET[r] + s
            for byte in b:
                if byte == 0: s = "1" + s
                else: break
            return s or "1"
        def dec(s):
            n = 0
            for c in s: n = n * 58 + ALPHABET.index(c)
            return n.to_bytes((n.bit_length() + 7) // 8, "big")
        result = {"Base58 Encode": enc(t.encode())}
        try: result["Base58 Decode"] = dec(t).decode(errors="ignore")[:500]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Base58: {str(e)[:120]}")


@app.route("/api/octal", methods=["POST"])
@login_required
def api_octal():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        result = {"Octal Encode": " ".join(format(ord(c), "o") for c in t)}
        try:
            parts = t.split()
            if all(p.isdigit() for p in parts):
                result["Octal Decode"] = "".join(chr(int(p, 8)) for p in parts)[:500]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Octal: {str(e)[:120]}")


@app.route("/api/decimal", methods=["POST"])
@login_required
def api_decimal():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        result = {"Decimal Encode": " ".join(str(ord(c)) for c in t)}
        try:
            parts = t.split()
            if all(p.isdigit() for p in parts):
                result["Decimal Decode"] = "".join(chr(int(p)) for p in parts)[:500]
        except Exception: pass
        return ok(result)
    except Exception as e: return err(f"Decimal: {str(e)[:120]}")


@app.route("/api/reverse", methods=["POST"])
@login_required
def api_reverse():
    try:
        d = request.get_json(silent=True) or {}
        return ok({"Ters": d.get("text","")[:5000][::-1]})
    except Exception as e: return err(f"Reverse: {str(e)[:120]}")


@app.route("/api/case", methods=["POST"])
@login_required
def api_case():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:5000]
        return ok({"upper": t.upper(), "lower": t.lower(), "title": t.title(), "capitalize": t.capitalize(), "swapcase": t.swapcase()})
    except Exception as e: return err(f"Case: {str(e)[:120]}")


@app.route("/api/wordcount", methods=["POST"])
@login_required
def api_wordcount():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:100000]
        return ok({"karakter": len(t), "kelime": len(t.split()), "satır": len(t.splitlines())})
    except Exception as e: return err(f"WordCount: {str(e)[:120]}")


@app.route("/api/uniq", methods=["POST"])
@login_required
def api_uniq():
    try:
        d = request.get_json(silent=True) or {}
        t = d.get("text","")[:50000]
        seen = set(); out = []
        for line in t.splitlines():
            if line not in seen: seen.add(line); out.append(line)
        return ok({"satır": "\n".join(out), "toplam": len(t.splitlines()), "tekil": len(out)})
    except Exception as e: return err(f"Uniq: {str(e)[:120]}")


@app.route("/api/sortlines", methods=["POST"])
@login_required
def api_sortlines():
    try:
        d = request.get_json(silent=True) or {}
        return ok({"sıralı": "\n".join(sorted(d.get("text","")[:50000].splitlines()))})
    except Exception as e: return err(f"SortLines: {str(e)[:120]}")


@app.route("/download/<name>")
@login_required
def download(name):
    try:
        safe = os.path.basename(name)
        if not re.match(r'^[a-zA-Z0-9_.-]+\.(html|zip|txt)$', safe): return "Geçersiz", 400
        f = (TEMP_DIR / safe).resolve()
        if TEMP_DIR.resolve() not in f.parents: return "Yasak", 403
        if f.exists() and f.is_file(): return send_file(str(f), as_attachment=True)
    except Exception: pass
    return "Dosya yok", 404


@app.errorhandler(404)
def e404(e): return jsonify({"status":"error","message":"Bulunamadı"}), 404

@app.errorhandler(413)
def e413(e): return jsonify({"status":"error","message":"İstek çok büyük"}), 413

@app.errorhandler(429)
def e429(e): return jsonify({"status":"error","message":"Rate limit aşıldı"}), 429

@app.errorhandler(Exception)
def eall(e):
    import traceback
    traceback.print_exc()
    return jsonify({"status":"error","message":"Sunucu hatası"}), 500


if __name__ == "__main__":
    print()
    print("=" * 62)
    print("  p1sy  -  by grego | p1sy")
    print("=" * 62)
    print(f"  Mod:     {ENV_MODE}")
    print(f"  Admin:   {ADMIN_USER}")
    HOST = os.getenv("HOST", "0.0.0.0")
    PORT = int(os.getenv("PORT", "5000"))
    print(f"  Host:    {HOST}")
    print(f"  Port:    {PORT}")
    print(f"  Allowed: {sorted(ALLOWED_IPS) if ALLOWED_IPS else 'public access'}")
    print(f"  Static:  {STATIC_DIR}")
    print("=" * 62)
    print(f"  Tarayicidan: http://127.0.0.1:{PORT}")
    print("  Araç sayısı: 215")
    print("  Müzik için: static/baba.mp3 koy")
    print("=" * 62)
    print()
    app.run(host=HOST, port=PORT, debug=False, threaded=True)