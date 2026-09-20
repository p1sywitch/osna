const express = require("express");
const session = require("express-session");
const rateLimit = require("express-rate-limit");
const bcrypt = require("bcryptjs");
const axios = require("axios");
const dns = require("dns").promises;
const net = require("net");
const crypto = require("crypto");
const fs = require("fs");
const path = require("path");
const os = require("os");
const {execFile} = require("child_process");
const dotenv = require("dotenv");
const QRCode = require("qrcode");
const cheerio = require("cheerio");

const BASE_DIR = __dirname;
dotenv.config({path:path.join(BASE_DIR, ".env")});

const ADMIN_USER = (process.env.OWNER_USERNAME || process.env.TOOLBOX_ADMIN_USERNAME || "").trim();
const ADMIN_PASS = process.env.OWNER_PASSWORD || process.env.TOOLBOX_ADMIN_PASSWORD || "";
const SECRET_KEY = process.env.TOOLBOX_SECRET_KEY || "";
const ENV_MODE = (process.env.ENV_MODE || process.env.TOOLBOX_ENV || "production").trim().toLowerCase();
const HOST = process.env.HOST || "0.0.0.0";
const PORT = Number(process.env.PORT || 5000);

if (!ADMIN_USER || ADMIN_PASS.length < 12 || SECRET_KEY.length < 32) {
  console.error("\n[GÜVENLİK HATASI]");
  if (!ADMIN_USER) console.error("  - OWNER_USERNAME .env içinde ayarlanmalı");
  if (ADMIN_PASS.length < 12) console.error("  - OWNER_PASSWORD en az 12 karakter olmalı");
  if (SECRET_KEY.length < 32) console.error("  - TOOLBOX_SECRET_KEY en az 32 karakter olmalı");
  console.error("\n.env dosyasını oluştur.");
  process.exit(1);
}

const app = express();
app.disable("x-powered-by");
app.use(express.json({limit:"256kb"}));
app.use(express.urlencoded({extended:false,limit:"256kb"}));

const limiter = rateLimit({
  windowMs:60*60*1000, max:300,
  standardHeaders:true, legacyHeaders:false,
  message:{status:"error",message:"Rate limit aşıldı"}
});
app.use(limiter);

app.use(session({
  secret:SECRET_KEY,
  resave:false,
  saveUninitialized:false,
  cookie:{
    httpOnly:true,
    sameSite:"lax",
    secure:ENV_MODE==="production",
    maxAge:3600*1000
  }
}));

const LOG_FILE = path.join(BASE_DIR,"logs.txt");
const USERS_FILE = path.join(BASE_DIR,"users.json");
const TEMP_DIR = path.join(os.tmpdir(),"p1sy_files");
fs.mkdirSync(TEMP_DIR,{recursive:true});
if (!fs.existsSync(LOG_FILE)) fs.writeFileSync(LOG_FILE,"","utf8");

function readUsers(){
  try { return JSON.parse(fs.readFileSync(USERS_FILE,"utf8")); }
  catch { return []; }
}
function writeUsers(users){ fs.writeFileSync(USERS_FILE,JSON.stringify(users,null,2),"utf8"); }
function logEvent(event,extra=""){
  const safe=String(extra||"").replace(ADMIN_PASS,"[REDACTED]").slice(0,420);
  try { fs.appendFileSync(LOG_FILE,`[${new Date().toISOString()}] [${event}] ${safe}\n`); } catch {}
}
function ok(res,data={},message="Başarılı"){ return res.json({status:"ok",message,data}); }
function err(res,msg,code=200){ return res.status(code).json({status:"error",message:String(msg).slice(0,300)}); }
function logged(req){ return !!req.session.logged_in; }
function admin(req){ return logged(req) && (req.session.role==="admin" || req.session.username===ADMIN_USER); }
function loginRequired(req,res,next){ if(!logged(req)) return err(res,"Giriş gerekli",401); next(); }
function adminRequired(req,res,next){ if(!logged(req)) return err(res,"Giriş gerekli",401); if(!admin(req)) return err(res,"Admin yetkisi gerekli",403); next(); }

function validHost(host){ return typeof host==="string" && /^[A-Za-z0-9.-]{1,253}$/.test(host); }
function safePrivate(ip){
  if(!net.isIP(ip)) return false;
  if(ip.includes(":")){
    return ip==="::1" || ip.toLowerCase().startsWith("fc") || ip.toLowerCase().startsWith("fd") || ip.toLowerCase().startsWith("fe80");
  }
  const p=ip.split(".").map(Number);
  return p[0]===10 || (p[0]===172&&p[1]>=16&&p[1]<=31) || (p[0]===192&&p[1]===168) || p[0]===127 || p[0]===169&&p[1]===254 || p[0]===0 || (p[0]===100&&p[1]>=64&&p[1]<=127);
}
async function resolveSafe(host){
  const all=[...(await dns.resolve4(host).catch(()=>[])),...(await dns.resolve6(host).catch(()=>[]))];
  if(!all.length) throw new Error("DNS çözümlenemedi");
  for(const ip of all) if(safePrivate(ip)) throw new Error("Yasaklı/özel IP");
  return all;
}
function makeUrl(u){
  u=String(u||"").trim();
  if(!/^https?:\/\//i.test(u)) u="https://"+u;
  const x=new URL(u);
  if(!["http:","https:"].includes(x.protocol)||!x.hostname) throw new Error("Geçersiz URL");
  return x;
}
async function safeGet(u,opts={}){
  const url=makeUrl(u);
  await resolveSafe(url.hostname);
  return axios.get(url.toString(),{
    timeout:10000,maxRedirects:0,validateStatus:()=>true,
    headers:{"User-Agent":"Mozilla/5.0 (compatible; p1syWeb/2.0)"},...opts
  });
}
function body(req){ return req.body && typeof req.body==="object" ? req.body : {}; }
function text(req){ return String(body(req).text||"").slice(0,50000); }

app.use((req,res,next)=>{
  if(!req.path.startsWith("/static/")){
    res.set("X-Content-Type-Options","nosniff");
    res.set("X-Frame-Options","DENY");
    res.set("Referrer-Policy","no-referrer");
    res.set("Permissions-Policy","geolocation=(), microphone=(), camera=()");
  }
  const allowed=(process.env.ALLOWED_IPS||"").split(",").map(x=>x.trim()).filter(Boolean);
  if(allowed.length && !allowed.includes(req.ip.replace("::ffff:",""))) return err(res,"Erişim yok",403);
  next();
});

app.get("/",(req,res)=>{
  if(logged(req)) return res.redirect("/app");
  res.sendFile(path.join(BASE_DIR,"public","login.html"));
});
app.get("/app",(req,res)=>{
  if(!logged(req)) return res.redirect("/");
  res.sendFile(path.join(BASE_DIR,"public","app.html"));
});
app.get("/favicon.ico",(req,res)=>res.status(204).end());
app.use("/static",express.static(path.join(BASE_DIR,"public","static")));

// Auth
app.post("/api/register",rateLimit({windowMs:60000,max:5}),async(req,res)=>{
  const d=body(req), u=String(d.username||"").trim(), pw=String(d.password||"");
  if(!/^[A-Za-z0-9_.-]{3,32}$/.test(u)) return err(res,"Geçersiz kullanıcı adı");
  if(pw.length<8||pw.length>200) return err(res,"Şifre 8-200 karakter olmalı");
  const users=readUsers();
  if(users.some(x=>x.username===u)) return err(res,"Bu kullanıcı adı zaten kayıtlı");
  users.push({username:u,password_hash:await bcrypt.hash(pw,12),created_at:new Date().toISOString(),role:"user"});
  writeUsers(users);
  return ok(res,{username:u},"Kayıt başarılı, şimdi giriş yapabilirsin");
});
app.post("/api/login",rateLimit({windowMs:60000,max:10}),async(req,res)=>{
  const d=body(req), u=String(d.username||"").trim(), p=String(d.password||"");
  let valid=false;
  if(u===ADMIN_USER) valid=await bcrypt.compare(p,await bcrypt.hash(ADMIN_PASS,10));
  const users=readUsers(), row=users.find(x=>x.username===u);
  if(!valid && row) valid=await bcrypt.compare(p,row.password_hash);
  if(!valid){logEvent("LOGIN_FAIL","reason=invalid");return err(res,"Kullanıcı adı veya şifre hatalı");}
  req.session.regenerate(e=>{
    if(e) return err(res,"Oturum oluşturulamadı",500);
    req.session.logged_in=true; req.session.username=u; req.session.role=(u===ADMIN_USER?"admin":(row?.role||"user"));
    logEvent("LOGIN_OK",`user=${u}`);
    return ok(res,{username:u},"Giriş başarılı");
  });
});
app.post("/api/logout",(req,res)=>{logEvent("LOGOUT");req.session.destroy(()=>ok(res,{},"Çıkış"));});
app.post("/api/ping",loginRequired,(req,res)=>ok(res,{pong:true}));
app.get("/api/whoami",(req,res)=>ok(res,{logged_in:logged(req),username:req.session.username||null,role:req.session.role||null}));
app.post("/api/admin/users",adminRequired,(req,res)=>ok(res,readUsers().map(x=>({username:x.username,created_at:x.created_at,role:x.role}))));
app.post("/api/admin/role",adminRequired,(req,res)=>{
  const d=body(req), u=String(d.username||"").trim(), role=String(d.role||"").toLowerCase(), action=String(d.action||"grant").toLowerCase();
  if(!u||!["vip","founder"].includes(role)||!["grant","revoke"].includes(action)) return err(res,"username + role(vip/founder) + action(grant/revoke) gerekli");
  const users=readUsers(), row=users.find(x=>x.username===u); if(!row)return err(res,"Kullanıcı bulunamadı",404);
  row.role=action==="grant"?role:"user"; writeUsers(users); logEvent("ROLE_CHANGE",`target=${u} role=${role} action=${action}`);
  ok(res,{username:u,role:row.role},"Rol güncellendi");
});
app.post("/api/admin/logs",adminRequired,(req,res)=>{
  const n=Math.max(1,Math.min(Number(body(req).limit||100),500));
  const logs=fs.readFileSync(LOG_FILE,"utf8").split(/\r?\n/).filter(Boolean).slice(-n);
  ok(res,{count:logs.length,logs});
});

// Basic network / web tools
app.post("/api/ip",loginRequired,(req,res)=>ok(res,{ip:String(body(req).ip||"").trim(),valid:net.isIP(String(body(req).ip||"").trim())>0}));
app.post("/api/cidr",loginRequired,(req,res)=>{const x=String(body(req).cidr||body(req).text||""); const m=x.match(/^(.+)\/(\d+)$/); if(!m)return err(res,"Geçersiz CIDR"); const bits=net.isIP(m[1]); const n=Number(m[2]); if(!bits||n<0||n>(bits===4?32:128))return err(res,"Geçersiz CIDR"); ok(res,{valid:true});});
app.post("/api/rdns",loginRequired,async(req,res)=>{try{const ip=String(body(req).ip||"").trim();ok(res,{ip,hostnames:await dns.reverse(ip)});}catch(e){err(res,"RDNS: "+e.message)}});
app.post("/api/dns",loginRequired,async(req,res)=>{try{const d=String(body(req).domain||"").trim(); if(!validHost(d))return err(res,"Geçersiz domain"); const out={}; for(const t of ["A","AAAA","MX","TXT","NS","CNAME"]){try{out[t]=await dns.resolve(d,t)}catch{out[t]=[]}} ok(res,out);}catch(e){err(res,e.message)}});
app.post("/api/ipv6",loginRequired,async(req,res)=>{try{const d=String(body(req).domain||"").trim();ok(res,await dns.resolve6(d));}catch(e){err(res,"IPv6: "+e.message)}});
app.post("/api/subdomains",loginRequired,async(req,res)=>{const d=String(body(req).domain||"").trim(); if(!validHost(d))return err(res,"Geçersiz"); const subs=["www","mail","ftp","api","dev","test","staging","admin","blog","shop","app","m","mobile","cdn","static","img","images","docs","support","help","forum","secure","vpn","portal","git","jenkins"]; const out=[]; await Promise.all(subs.map(async s=>{try{const a=await dns.resolve4(`${s}.${d}`);out.push({subdomain:`${s}.${d}`,ip:a[0]});}catch{}}));out.sort((a,b)=>a.subdomain.localeCompare(b.subdomain));ok(res,out);});
app.post("/api/portscan",loginRequired,async(req,res)=>{try{const h=String(body(req).host||"").trim();if(!validHost(h))return err(res,"Geçersiz host");const ip=(await dns.resolve4(h))[0];let ports=[21,22,23,25,53,80,110,143,443,445,993,995,1433,1521,3306,3389,5432,5900,6379,8080,8443,27017];const r=String(body(req).range||"");if(/^\d+-\d+$/.test(r)){const [a,b]=r.split("-").map(Number);if(a<1||b>65535||b-a>1000)return err(res,"Port aralığı geçersiz (max 1000)");ports=Array.from({length:b-a+1},(_,i)=>a+i)}const open=[];await Promise.all(ports.map(p=>new Promise(done=>{const s=new net.Socket();s.setTimeout(700);s.once("connect",()=>{open.push({port:p});s.destroy();done()});s.once("error",()=>{s.destroy();done()});s.once("timeout",()=>{s.destroy();done()});s.connect(p,ip)})));open.sort((a,b)=>a.port-b.port);ok(res,{ip,open,total:ports.length});}catch(e){err(res,"Portscan: "+e.message)}});
app.post("/api/banner",loginRequired,(req,res)=>{const h=String(body(req).host||"").trim(),p=Number(body(req).port||22);if(!validHost(h)||p<1||p>65535)return err(res,"Geçersiz host/port");const s=new net.Socket();let done=false;const finish=(o)=>{if(done)return;done=true;try{s.destroy()}catch{};o()};s.setTimeout(5000);s.on("connect",()=>{s.write("\r\n");});s.on("data",d=>finish(()=>ok(res,{banner:d.toString("utf8").slice(0,1000)})));s.on("timeout",()=>finish(()=>err(res,"Zaman aşımı")));s.on("error",e=>finish(()=>err(res,"Banner: "+e.message)));s.connect(p,h);});
app.post("/api/headers",loginRequired,async(req,res)=>{try{const r=await safeGet(body(req).url,{maxRedirects:0});ok(res,{Status:r.status,URL:r.config.url,Headers:r.headers});}catch(e){err(res,"Header: "+e.message)}});
app.post("/api/robots",loginRequired,async(req,res)=>{try{const h=String(body(req).url||"").replace(/^https?:\/\//,"").replace(/\/.*$/,"");const r=await safeGet(`https://${h}/robots.txt`);ok(res,{status:r.status,content:String(r.data).slice(0,8000)});}catch(e){err(res,e.message)}});
app.post("/api/sitemap",loginRequired,async(req,res)=>{try{const h=String(body(req).url||"").replace(/^https?:\/\//,"").replace(/\/.*$/,"");const r=await safeGet(`https://${h}/sitemap.xml`);ok(res,{status:r.status,content:String(r.data).slice(0,8000)});}catch(e){err(res,e.message)}});
app.post("/api/redirect",loginRequired,async(req,res)=>{try{const r=await safeGet(body(req).url);ok(res,{status:r.status,location:r.headers.location||null});}catch(e){err(res,e.message)}});

// Encoding / generator tools
app.post("/api/hash",loginRequired,(req,res)=>{const t=text(req),algo=String(body(req).algo||"sha256").toLowerCase();if(!["md5","sha1","sha256","sha512"].includes(algo))return err(res,"Algoritma");ok(res,{hash:crypto.createHash(algo).update(t).digest("hex")});});
app.post("/api/hex",loginRequired,(req,res)=>ok(res,{result:Buffer.from(text(req),"utf8").toString("hex")}));
app.post("/api/base32",loginRequired,(req,res)=>{const t=text(req);const alphabet="ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";let bits="";for(const b of Buffer.from(t))bits+=b.toString(2).padStart(8,"0");let out="";for(let i=0;i<bits.length;i+=5)out+=alphabet[parseInt(bits.slice(i,i+5).padEnd(5,"0"),2)];while(out.length%8)out+="=";ok(res,{result:out});});
app.post("/api/binary",loginRequired,(req,res)=>ok(res,{result:[...Buffer.from(text(req))].map(b=>b.toString(2).padStart(8,"0")).join(" ")}));
app.post("/api/rot13",loginRequired,(req,res)=>ok(res,{result:text(req).replace(/[a-zA-Z]/g,c=>String.fromCharCode(c.charCodeAt(0)+(c.toLowerCase()<= "m"?13:-13)))}));
app.post("/api/urlencode",loginRequired,(req,res)=>ok(res,{result:encodeURIComponent(text(req))}));
app.post("/api/htmlentity",loginRequired,(req,res)=>ok(res,{result:text(req).replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]))}));
app.post("/api/jsonfmt",loginRequired,(req,res)=>{try{ok(res,{result:JSON.stringify(JSON.parse(text(req)),null,2)})}catch(e){err(res,"Geçersiz JSON")}});
app.post("/api/reverse",loginRequired,(req,res)=>ok(res,{result:text(req).split("").reverse().join("")}));
app.post("/api/case",loginRequired,(req,res)=>{const mode=String(body(req).mode||"upper");const t=text(req);ok(res,{result:mode==="lower"?t.toLowerCase():mode==="title"?t.replace(/\w\S*/g,x=>x[0].toUpperCase()+x.slice(1).toLowerCase()):t.toUpperCase()});});
app.post("/api/wordcount",loginRequired,(req,res)=>{const t=text(req);ok(res,{words:t.trim()?t.trim().split(/\s+/).length:0,chars:t.length,lines:t.split(/\r?\n/).length});});
app.post("/api/uniq",loginRequired,(req,res)=>{const a=text(req).split(/\r?\n/);ok(res,{result:[...new Set(a)].join("\n")});});
app.post("/api/sortlines",loginRequired,(req,res)=>ok(res,{sıralı:text(req).split(/\r?\n/).sort().join("\n")}));
app.post("/api/randstr",loginRequired,(req,res)=>{const n=Math.max(1,Math.min(Number(body(req).length||16),10000));const chars=String(body(req).chars||"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789");let o="";for(let i=0;i<n;i++)o+=chars[crypto.randomInt(chars.length)];ok(res,{result:o});});
app.post("/api/passgen",loginRequired,(req,res)=>{const n=Math.max(8,Math.min(Number(body(req).length||20),200));const chars="ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz23456789!@#$%^&*";let o="";for(let i=0;i<n;i++)o+=chars[crypto.randomInt(chars.length)];ok(res,{password:o});});
app.post("/api/uuid",loginRequired,(req,res)=>ok(res,{uuid:crypto.randomUUID()}));
app.post("/api/luhn",loginRequired,(req,res)=>{const s=text(req).replace(/\D/g,"");let sum=0,alt=false;for(let i=s.length-1;i>=0;i--){let n=+s[i];if(alt){n*=2;if(n>9)n-=9}sum+=n;alt=!alt}ok(res,{valid:s.length>0&&sum%10===0});});
app.post("/api/qr",loginRequired,async(req,res)=>{try{const data=String(body(req).text||body(req).data||"");const url=await QRCode.toDataURL(data);ok(res,{dataUrl:url});}catch(e){err(res,e.message)}});

// Generic extra tool endpoint, covering the large utility collection in the original app.
app.post("/api/extra/:op",loginRequired,(req,res)=>{
  try{
    const op=req.params.op, t=text(req), lines=t.split(/\r?\n/), words=t.trim()?t.trim().split(/\s+/):[];
    let out;
    if(op==="upper"||op==="upper_lines") out=t.toUpperCase();
    else if(op==="lower"||op==="lower_lines") out=t.toLowerCase();
    else if(op==="title"||op==="title_lines") out=t.replace(/\w\S*/g,x=>x[0].toUpperCase()+x.slice(1).toLowerCase());
    else if(op==="trim"||op==="trim_lines") out=t.trim();
    else if(op==="reverse") out=[...t].reverse().join("");
    else if(op==="reverse_words") out=words.reverse().join(" ");
    else if(op==="reverse_lines") out=[...lines].reverse().join("\n");
    else if(op==="linecount"||op==="linecount_nonempty") out=op==="linecount"?lines.length:lines.filter(x=>x.trim()).length;
    else if(op==="charcount") out=t.length;
    else if(op==="wordcount") out=words.length;
    else if(op==="uniq"||op==="dedupe_words"||op==="unique_words") out=[...new Set(op==="uniq"?lines:words)].join(op==="uniq"?"\n":" ");
    else if(op==="sort"||op==="sort_words") out=(op==="sort"?lines:words).sort((a,b)=>a.localeCompare(b)).join(op==="sort"?"\n":" ");
    else if(op==="sortrev"||op==="sort_words_rev") out=(op==="sortrev"?lines:words).sort((a,b)=>b.localeCompare(a)).join(op==="sortrev"?"\n":" ");
    else if(op==="digits") out=t.replace(/\D/g,"");
    else if(op==="letters") out=[...t].filter(c=>/[^\W\d_]/u.test(c)).join("");
    else if(op==="alnum") out=[...t].filter(c=>/[A-Za-z0-9]/.test(c)).join("");
    else if(op==="spaces") out=t.replace(/\s+/g," ").trim();
    else if(op==="noblank"||op==="remove_blank_lines") out=lines.filter(x=>x.trim()).join("\n");
    else if(op==="linenum") out=lines.map((x,i)=>`${i+1}: ${x}`).join("\n");
    else if(op==="slug"||op==="slug_strict") out=t.toLowerCase().replace(/[^a-z0-9]+/g,"-").replace(/^-|-$/g,"");
    else if(op==="snake"||op==="snake_strict") out=t.replace(/[^A-Za-z0-9]+/g,"_").replace(/^_|_$/g,"").toLowerCase();
    else if(op==="kebab"||op==="kebab_strict") out=t.replace(/[^A-Za-z0-9]+/g,"-").replace(/^-|-$/g,"").toLowerCase();
    else if(op==="dotcase"||op==="dot_strict") out=t.replace(/[^A-Za-z0-9]+/g,".").replace(/^\.|\.$/g,"").toLowerCase();
    else if(op==="repeat5") out=t.repeat(5);
    else if(op==="repeat10") out=t.repeat(10);
    else if(op==="repeat2") out=t.repeat(2);
    else if(op==="repeat3") out=t.repeat(3);
    else if(op==="b64enc") out=Buffer.from(t).toString("base64");
    else if(op==="b64dec") out=Buffer.from(t,"base64").toString("utf8");
    else if(op==="hexenc") out=Buffer.from(t).toString("hex");
    else if(op==="hexdec") out=Buffer.from(t,"hex").toString("utf8");
    else if(op==="md5"||op==="sha1"||op==="sha256"||op==="sha512") out=crypto.createHash(op).update(t).digest("hex");
    else if(op==="uuid"||op==="random_uuid") out=crypto.randomUUID();
    else if(op==="random_hex16") out=crypto.randomBytes(8).toString("hex");
    else if(op==="random_hex32") out=crypto.randomBytes(16).toString("hex");
    else if(op==="random_url_token"||op==="url_safe_token") out=crypto.randomBytes(16).toString("base64url");
    else if(op==="is_even") out=/^-?\d+$/.test(t)&&Number(t)%2===0;
    else if(op==="is_odd") out=/^-?\d+$/.test(t)&&Number(t)%2!==0;
    else if(op==="port_valid") out=/^\d+$/.test(t)&&+t>=1&&+t<=65535;
    else if(op==="email_valid") out=/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(t);
    else if(op==="url_valid"){try{const u=new URL(t);out=["http:","https:"].includes(u.protocol)&&!!u.hostname}catch{out=false}}
    else if(op==="domain_extract"||op==="hostname_valid"){try{out=op==="hostname_valid"?/^[A-Za-z0-9.-]{1,253}$/.test(t):(new URL(t.includes("://")?t:"https://"+t).hostname||"")}catch{out=false}}
    else if(op==="path_extract") out=new URL(t).pathname;
    else if(op==="query_params") out=Object.fromEntries(new URL(t).searchParams.entries());
    else if(op==="fragment_extract") out=new URL(t).hash.slice(1);
    else if(op==="scheme_extract") out=new URL(t).protocol.replace(":","");
    else if(op==="jsonvalid"){try{JSON.parse(t);out=true}catch{out=false}}
    else if(op==="jsonpretty") out=JSON.stringify(JSON.parse(t),null,2);
    else if(op==="jsonmin") out=JSON.stringify(JSON.parse(t));
    else if(op==="html_escape2") out=t.replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
    else if(op==="strip_tags2") out=t.replace(/<[^>]+>/g,"");
    else if(op==="palindrome"||op==="palindrome_clean"){const x=op==="palindrome_clean"?t.toLowerCase().replace(/[^a-z0-9]/g,""):t;out=x===[...x].reverse().join("")}
    else if(op==="number_list") out=(t.match(/-?\d+(?:\.\d+)?/g)||[]).map(Number);
    else if(op==="number_sum") out=(t.match(/-?\d+(?:\.\d+)?/g)||[]).reduce((a,b)=>a+Number(b),0);
    else if(op==="factorial"){const n=Number(t);if(!Number.isInteger(n)||n<0||n>1000)out="0-1000 arası tam sayı gerekli";else{let z=1n;for(let i=2n;i<=BigInt(n);i++)z*=i;out=z.toString()}}
    else if(op==="nowts"||op==="timestamp_ms") out=op==="nowts"?Math.floor(Date.now()/1000):Date.now();
    else if(op==="nowiso"||op==="utc_iso") out=new Date().toISOString();
    else if(op==="year") out=new Date().getFullYear();
    else if(op==="month") out=new Date().getMonth()+1;
    else if(op==="day") out=new Date().getDate();
    else if(op==="hour") out=new Date().getHours();
    else if(op==="minute") out=new Date().getMinutes();
    else if(op==="second") out=new Date().getSeconds();
    else if(op==="random_bytes16") out=crypto.randomBytes(16).toString("base64");
    else return err(res,"Bilinmeyen araç",404);
    return ok(res,{input:t,result:out});
  }catch(e){return err(res,"Extra: "+e.message)}
});

// Compatibility placeholders for the remaining named endpoints.
const compatibility = [
  "mac","email","phone","usercheck","trace","ssl","headersec","cookie","methods","sectxt","waf",
  "cve","copy","copyfull","viewsrc","pagetext","hashid","passstrength","jwt","whois","urlparse",
  "wayback","discord","discordid","github","reddit","zonetr","short","urlshort","sysinfo","myip",
  "mime","httpstatus","chmod","portinfo","octal","decimal","lorem","timestamp","ipport","fakeip",
  "fakenum","fakecard","faketc","emailgen","diff"
];
for(const name of compatibility){
  app.post(`/api/${name}`,loginRequired,async(req,res)=>{
    try{
      if(name==="myip") return ok(res,{ip:(req.headers["x-forwarded-for"]||req.socket.remoteAddress||"").split(",")[0].trim()});
      if(name==="sysinfo") return ok(res,{platform:process.platform,node:process.version,arch:process.arch,memory:process.memoryUsage().rss});
      if(name==="uuid") return ok(res,{uuid:crypto.randomUUID()});
      if(name==="timestamp") return ok(res,{timestamp:Math.floor(Date.now()/1000),iso:new Date().toISOString()});
      if(name==="hashid") return ok(res,{result:crypto.createHash("sha256").update(text(req)).digest("hex")});
      if(name==="discordid"){const id=String(body(req).id||body(req).text||""); if(!/^\d{17,20}$/.test(id))return err(res,"Geçersiz Discord ID"); const created=new Date(Number(BigInt(id)>>22n)+1420070400000); return ok(res,{id,created_at:created.toISOString(),default_avatar:`https://cdn.discordapp.com/embed/avatars/${Number(BigInt(id)>>22n)%6}.png`});}
      return err(res,`${name} aracı Node sürümünde henüz uygulanmadı`,501);
    }catch(e){return err(res,`${name}: ${e.message}`)}
  });
}

app.get("/download/:name",loginRequired,(req,res)=>{
  const name=path.basename(req.params.name);
  if(!/^[A-Za-z0-9_.-]+\.(html|zip|txt)$/.test(name))return res.status(400).send("Geçersiz");
  const f=path.resolve(TEMP_DIR,name);
  if(!f.startsWith(path.resolve(TEMP_DIR)+path.sep))return res.status(403).send("Yasak");
  if(fs.existsSync(f))return res.download(f); res.status(404).send("Dosya yok");
});
app.use((req,res)=>err(res,"Bulunamadı",404));
app.use((e,req,res,next)=>{console.error(e);err(res,"Sunucu hatası",500);});

app.listen(PORT,HOST,()=>console.log(`p1sy TOOLBOX Node.js | http://${HOST}:${PORT}`));
