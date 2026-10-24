"""
多人实时聊天室（微信风格界面）—— 单文件版
运行：
    pip install fastapi "uvicorn[standard]"
    python chat_server.py
然后在浏览器打开 http://localhost:8000
同一 Wi-Fi / 局域网的人打开 http://<你电脑的IP>:8000 即可加入
"""

import json
import socket
from collections import deque
import time
from datetime import datetime

import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse

app = FastAPI()

HISTORY_SIZE = 50          # 新加入的人能看到的最近消息条数
MAX_MSG_LEN = 1000         # 单条消息最大长度
MAX_NAME_LEN = 20          # 昵称最大长度
MAX_AVATAR_LEN = 200_000   # 头像（压缩后的图片）最大长度


class ChatRoom:
    def __init__(self):
        self.clients: dict[WebSocket, str] = {}   # 连接 -> 昵称
        self.history: deque = deque(maxlen=HISTORY_SIZE)
        self.avatars: dict[str, str] = {}         # 昵称 -> 头像图片(data URL)

    def names(self):
        return sorted(self.clients.values())

    async def broadcast(self, payload: dict, save=True):
        if save:
            self.history.append(payload)
        text = json.dumps(payload, ensure_ascii=False)
        dead = []
        for ws in self.clients:
            try:
                await ws.send_text(text)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.clients.pop(ws, None)

    async def send_users(self):
        await self.broadcast({"type": "users", "users": self.names()}, save=False)

    async def send_avatars(self):
        await self.broadcast({"type": "avatars", "avatars": self.avatars}, save=False)

    def unique_name(self, name: str) -> str:
        """昵称重复时自动加编号"""
        taken = set(self.clients.values())
        if name not in taken:
            return name
        i = 2
        while f"{name}({i})" in taken:
            i += 1
        return f"{name}({i})"


room = ChatRoom()


def valid_avatar(a) -> bool:
    return isinstance(a, str) and a.startswith("data:image/") and len(a) <= MAX_AVATAR_LEN


def now():
    return datetime.now().strftime("%H:%M")


@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    name = None
    try:
        # 第一条消息必须是 {"type": "join", "name": "..."}
        first = json.loads(await ws.receive_text())
        raw = str(first.get("name", "")).strip()[:MAX_NAME_LEN] or "匿名"
        name = room.unique_name(raw)
        if valid_avatar(first.get("avatar")):
            room.avatars[name] = first["avatar"]

        # 先把历史记录和最终昵称发给新用户
        await ws.send_text(json.dumps(
            {"type": "welcome", "name": name, "history": list(room.history), "avatars": room.avatars},
            ensure_ascii=False))

        room.clients[ws] = name
        await room.broadcast({"type": "system", "text": f"{name} 加入了聊天室", "time": now(), "ts": int(time.time() * 1000)})
        await room.send_users()
        await room.send_avatars()

        while True:
            data = json.loads(await ws.receive_text())
            if data.get("type") == "avatar":
                if valid_avatar(data.get("avatar")):
                    room.avatars[name] = data["avatar"]
                elif data.get("avatar") is None:
                    room.avatars.pop(name, None)
                await room.send_avatars()
                continue
            text = str(data.get("text", "")).strip()[:MAX_MSG_LEN]
            if text:
                await room.broadcast({"type": "chat", "name": name, "text": text, "time": now(), "ts": int(time.time() * 1000)})

    except (WebSocketDisconnect, json.JSONDecodeError):
        pass
    finally:
        if ws in room.clients:
            room.clients.pop(ws)
            await room.broadcast({"type": "system", "text": f"{name} 离开了聊天室", "time": now(), "ts": int(time.time() * 1000)})
            await room.send_users()


@app.get("/")
async def index():
    return HTMLResponse(PAGE)


PAGE = r"""<!doctype html>
<html lang="zh">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>群聊</title>
<style>
  :root { --bg:#ededed; --bar:#ededed; --input-bar:#f7f7f7; --field:#fff; --fg:#191919; --muted:#8a8a8a; --line:#d9d9d9;
          --other:#fff; --me:#95ec69; --me-fg:#191919; --green:#07c160; --green-press:#06ad56; }
  @media (prefers-color-scheme: dark) {
    :root { --bg:#111; --bar:#191919; --input-bar:#1e1e1e; --field:#2c2c2c; --fg:#e5e5e5; --muted:#7d7d7d; --line:#2a2a2a;
            --other:#2c2c2c; --me:#3eb575; --me-fg:#0d0d0d; color-scheme:dark; }
  }
  * { box-sizing:border-box; }
  html, body { height:100%; margin:0; }
  body { background:var(--bg); color:var(--fg); font-family:-apple-system,BlinkMacSystemFont,"PingFang SC","Hiragino Sans GB","Microsoft YaHei",sans-serif; font-size:16px; }
  .app { height:100%; display:flex; flex-direction:column; max-width:760px; margin:0 auto; }
  header { flex:none; height:48px; display:flex; align-items:center; justify-content:center; position:relative;
           background:var(--bar); border-bottom:.5px solid var(--line); padding-top:env(safe-area-inset-top,0px); box-sizing:content-box; }
  header h1 { margin:0; font-size:17px; font-weight:600; }
  header h1 span { font-weight:400; }
  #status { position:absolute; left:12px; font-size:12px; color:var(--muted); }
  #list { flex:1; overflow-y:auto; padding:12px; display:flex; flex-direction:column; gap:16px; }
  .time { align-self:center; font-size:12px; color:var(--muted); }
  .sys { align-self:center; font-size:12px; color:var(--muted); background:rgba(0,0,0,.06); padding:3px 8px; border-radius:4px; }
  .msg { display:flex; gap:10px; align-items:flex-start; }
  .msg.me { flex-direction:row-reverse; }
  .avatar { flex:none; width:40px; height:40px; border-radius:5px; color:#fff; font-size:16px; font-weight:600;
            display:flex; align-items:center; justify-content:center; }
  .body { display:flex; flex-direction:column; min-width:0; max-width:calc(100% - 110px); }
  .msg.me .body { align-items:flex-end; }
  .name { font-size:12px; color:var(--muted); margin:0 0 4px 2px; }
  .msg.me .name { display:none; }
  .bubble { position:relative; background:var(--other); padding:9px 12px; border-radius:5px; line-height:1.45;
            white-space:pre-wrap; word-break:break-word; overflow-wrap:anywhere; }
  .bubble::before { content:""; position:absolute; top:13px; left:-5px; width:10px; height:10px; background:inherit; transform:rotate(45deg); }
  .msg.me .bubble { background:var(--me); color:var(--me-fg); }
  .msg.me .bubble::before { left:auto; right:-5px; }
  footer { flex:none; display:flex; gap:8px; align-items:flex-end; background:var(--input-bar); border-top:.5px solid var(--line);
           padding:8px 12px calc(8px + env(safe-area-inset-bottom,0px)); }
  #text { flex:1; min-width:0; resize:none; border:none; outline:none; border-radius:5px; background:var(--field); color:var(--fg);
          font:inherit; line-height:1.4; padding:8px 10px; height:38px; max-height:120px; }
  #send { flex:none; height:38px; padding:0 16px; border:none; border-radius:5px; background:var(--green); color:#fff; font:inherit; font-size:15px; cursor:pointer; }
  #send:disabled { opacity:.45; cursor:default; }
  #send:hover:not(:disabled) { background:var(--green-press); }
  .sheet-wrap { position:fixed; inset:0; background:rgba(0,0,0,.45); display:flex; align-items:center; justify-content:center; padding:16px; }
  .sheet { background:var(--bar); border-radius:12px; width:min(100%,320px); padding:20px; display:flex; flex-direction:column; gap:14px; }
  .sheet h2 { margin:0; font-size:17px; text-align:center; }
  .sheet p { margin:0; font-size:13px; color:var(--muted); text-align:center; }
  #nick { border:none; outline:none; border-radius:6px; background:var(--field); color:var(--fg); font:inherit; padding:10px 12px; }
  #join { height:40px; border:none; border-radius:6px; background:var(--green); color:#fff; font:inherit; cursor:pointer; }
  #profileBtn { position:absolute; right:8px; background:none; border:none; color:var(--fg); font:inherit; font-size:14px; padding:6px 8px; border-radius:6px; cursor:pointer; }
  #profileBtn:hover { background:var(--line); }
  img.avatar { object-fit:cover; background:var(--line); }
  .msg.me .avatar { cursor:pointer; }
  .pick { display:flex; flex-direction:column; align-items:center; gap:8px; }
  #preview { width:72px; height:72px; border-radius:8px; font-size:28px; }
  .links { display:flex; gap:16px; }
  .links button { background:none; border:none; color:var(--green); font:inherit; font-size:14px; cursor:pointer; padding:4px; }
  .links button[hidden] { display:none; }
  .row2 { display:flex; gap:10px; }
  .row2 button { flex:1; }
  #cancel { height:40px; border:none; border-radius:6px; background:var(--field); color:var(--fg); font:inherit; cursor:pointer; }
  [hidden] { display:none !important; }
</style>
</head>
<body>
<div class="app">
  <header><span id="status"></span><h1>群聊<span id="count"></span></h1><button id="profileBtn" hidden>资料</button></header>
  <main id="list"></main>
  <footer>
    <textarea id="text" rows="1" placeholder="发消息" maxlength="1000"></textarea>
    <button id="send" disabled>发送</button>
  </footer>
</div>
<div class="sheet-wrap" id="sheet">
  <div class="sheet">
    <h2 id="sheetTitle">设置头像和昵称</h2>
    <div class="pick">
      <div id="preview" class="avatar"></div>
      <div class="links">
        <button id="choose" type="button">上传头像</button>
        <button id="clear" type="button" hidden>用默认头像</button>
      </div>
      <input type="file" id="file" accept="image/*" hidden>
    </div>
    <input id="nick" maxlength="20" placeholder="群昵称，比如：爸爸、加加" autofocus>
    <div class="row2">
      <button id="cancel" type="button" hidden>取消</button>
      <button id="join" type="button">进入群聊</button>
    </div>
  </div>
</div>
<script>
const $ = id => document.getElementById(id);
const list = $("list"), textEl = $("text"), sendBtn = $("send");
let ws, myName = "", lastTs = 0, joined = false;
let avatars = {};                 // 昵称 -> 头像图片
let myAvatar = null, draftAvatar = null;
try { myAvatar = localStorage.getItem("chatAvatar"); } catch (e) {}
const COLORS = ["#5b8ff9","#f6903d","#61ddaa","#e8684a","#9270ca","#269a99","#ff99c3","#d4a017"];
function colorOf(name) { let h = 0; for (const c of name) h = (h * 31 + c.codePointAt(0)) >>> 0; return COLORS[h % COLORS.length]; }

function makeAvatar(name, src) {
  if (src) { const img = document.createElement("img"); img.className = "avatar"; img.alt = ""; img.src = src; img.dataset.name = name; return img; }
  const d = document.createElement("div"); d.className = "avatar"; d.dataset.name = name;
  d.style.background = colorOf(name); d.textContent = [...name][0] || "?"; return d;
}
// 头像更新后，把页面上所有旧头像换掉
function refreshAvatars() {
  document.querySelectorAll("#list .avatar").forEach(el => {
    const n = el.dataset.name, fresh = makeAvatar(n, avatars[n]);
    if (n === myName) fresh.onclick = openSheet;
    el.replaceWith(fresh);
  });
}
function showPreview() {
  const p = $("preview"), name = $("nick").value.trim() || myName || "我";
  p.replaceChildren(); p.style.background = "";
  if (draftAvatar) { const img = document.createElement("img"); img.src = draftAvatar; img.style.cssText = "width:100%;height:100%;object-fit:cover;border-radius:8px"; p.append(img); }
  else { p.style.background = colorOf(name); p.textContent = [...name][0] || "?"; }
  $("clear").hidden = !draftAvatar;
}
// 把照片裁成正方形并压缩到 128×128，体积很小
function shrink(file) {
  return new Promise((res, rej) => {
    const url = URL.createObjectURL(file), img = new Image();
    img.onload = () => {
      const s = Math.min(img.width, img.height), c = document.createElement("canvas");
      c.width = c.height = 128;
      c.getContext("2d").drawImage(img, (img.width - s) / 2, (img.height - s) / 2, s, s, 0, 0, 128, 128);
      URL.revokeObjectURL(url); res(c.toDataURL("image/jpeg", 0.85));
    };
    img.onerror = rej; img.src = url;
  });
}
function openSheet() {
  draftAvatar = myAvatar; $("nick").value = myName; $("nick").disabled = true;
  $("sheetTitle").textContent = "换头像"; $("join").textContent = "保存"; $("cancel").hidden = false;
  showPreview(); $("sheet").hidden = false;
}

function fmtTime(ts) {
  const d = new Date(ts), now = new Date();
  const hm = d.toLocaleTimeString("zh-CN", { hour:"2-digit", minute:"2-digit", hour12:false });
  const day = x => new Date(x.getFullYear(), x.getMonth(), x.getDate()).getTime();
  const diff = Math.round((day(now) - day(d)) / 86400000);
  if (diff === 0) return hm;
  if (diff === 1) return "昨天 " + hm;
  return `${d.getMonth()+1}月${d.getDate()}日 ${hm}`;
}

function add(m) {
  const atBottom = list.scrollHeight - list.scrollTop - list.clientHeight < 80;
  const ts = m.ts || Date.now();
  if (ts - lastTs > 5 * 60 * 1000) {
    const t = document.createElement("div"); t.className = "time"; t.textContent = fmtTime(ts); list.append(t);
  }
  lastTs = ts;
  if (m.type === "system") {
    const s = document.createElement("div"); s.className = "sys"; s.textContent = m.text; list.append(s);
  } else if (m.type === "chat") {
    const mine = m.name === myName;
    const row = document.createElement("div"); row.className = "msg" + (mine ? " me" : "");
    const av = makeAvatar(m.name, avatars[m.name]);
    if (mine) av.onclick = openSheet;
    const body = document.createElement("div"); body.className = "body";
    const name = document.createElement("div"); name.className = "name"; name.textContent = m.name;
    const b = document.createElement("div"); b.className = "bubble"; b.textContent = m.text;
    body.append(name, b); row.append(av, body); list.append(row);
  }
  if (atBottom || m.name === myName) list.scrollTop = list.scrollHeight;
}

function connect(name) {
  const proto = location.protocol === "https:" ? "wss" : "ws";
  ws = new WebSocket(`${proto}://${location.host}/ws`);
  ws.onopen = () => { ws.send(JSON.stringify({ type:"join", name, avatar: myAvatar })); $("status").textContent = ""; };
  ws.onmessage = e => {
    const m = JSON.parse(e.data);
    if (m.type === "welcome") { myName = m.name; avatars = m.avatars || {}; list.replaceChildren(); lastTs = 0; m.history.forEach(add); list.scrollTop = list.scrollHeight; }
    else if (m.type === "avatars") { avatars = m.avatars; refreshAvatars(); }
    else if (m.type === "users") { $("count").textContent = `（${m.users.length}）`; }
    else add(m);
  };
  ws.onclose = () => { $("status").textContent = "连接中…"; setTimeout(() => connect(myName || name), 3000); };
}

function join() {
  if (joined) {                        // 已在群里：只是换头像
    myAvatar = draftAvatar;
    try { myAvatar ? localStorage.setItem("chatAvatar", myAvatar) : localStorage.removeItem("chatAvatar"); } catch (e) {}
    if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"avatar", avatar: myAvatar }));
    $("sheet").hidden = true; return;
  }
  const name = $("nick").value.trim();
  if (!name) return $("nick").focus();
  myAvatar = draftAvatar;
  try { localStorage.setItem("chatName", name); myAvatar ? localStorage.setItem("chatAvatar", myAvatar) : localStorage.removeItem("chatAvatar"); } catch (e) {}
  joined = true; $("profileBtn").hidden = false;
  $("sheet").hidden = true; connect(name); textEl.focus();
}
$("choose").onclick = () => $("file").click();
$("file").onchange = async () => {
  const f = $("file").files[0]; $("file").value = "";
  if (!f) return;
  try { draftAvatar = await shrink(f); showPreview(); } catch (e) { alert("这张图片打不开，换一张试试"); }
};
$("clear").onclick = () => { draftAvatar = null; showPreview(); };
$("cancel").onclick = () => { $("sheet").hidden = true; };
$("profileBtn").onclick = openSheet;
$("nick").oninput = showPreview;
function grow() { textEl.style.height = "38px"; textEl.style.height = Math.min(textEl.scrollHeight, 120) + "px"; sendBtn.disabled = !textEl.value.trim(); }
function send() {
  const text = textEl.value.trim();
  if (!text || !ws || ws.readyState !== 1) return;
  ws.send(JSON.stringify({ text })); textEl.value = ""; grow(); textEl.focus();
}
$("join").onclick = join;
$("nick").onkeydown = e => { if (e.key === "Enter" && !e.isComposing) join(); };
textEl.oninput = grow;
textEl.onkeydown = e => { if (e.key === "Enter" && !e.shiftKey && !e.isComposing) { e.preventDefault(); send(); } };
sendBtn.onclick = send;
try { $("nick").value = localStorage.getItem("chatName") || ""; } catch (e) {}
draftAvatar = myAvatar; showPreview();
</script>
</body>
</html>
"""


def local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


if __name__ == "__main__":
    import os
    port = int(os.environ.get("PORT", 8000))   # 云服务器会通过 PORT 告诉我们用哪个端口
    print(f"\n聊天室已启动！")
    print(f"  本机访问:   http://localhost:{port}")
    print(f"  局域网访问: http://{local_ip()}:{port}\n")
    uvicorn.run(app, host="0.0.0.0", port=port, log_level="warning")
