"""
多人实时聊天室（微信风格界面）—— 单文件版
功能：群聊 + 一对一私聊；文字 / 图片 / 视频消息；新消息提示音 + 系统通知（关掉页面也能收到）；语音 / 视频通话

运行：
    pip install -r requirements.txt
    python chat_server.py
然后在浏览器打开 http://localhost:8000
（通话和通知需要 https，部署到 Render 之后自动就是 https）

可选环境变量（在 Render 的 Environment 里设置，不设也能用）：
    VAPID_SECRET    任意一串随机字符，让推送密钥固定（不设时在 Render 上会自动用服务 ID 生成固定密钥）
    TURN_URLS       TURN 中转服务器地址，多个用逗号隔开，比如 turn:xxx:3478,turns:xxx:443
    TURN_USERNAME   TURN 用户名
    TURN_CREDENTIAL TURN 密码
    KEEP_AWAKE      设为 0 可关闭"防休眠"（默认在 Render 上每 10 分钟访问一下自己，避免免费实例睡着）
"""

import asyncio
import base64
import hashlib
import json
import os
import re
import secrets
import shutil
import socket
import time
import urllib.request
import uuid
from collections import deque
from datetime import datetime
from pathlib import Path
from urllib.parse import urlparse

import uvicorn
from fastapi import FastAPI, Request, WebSocket, WebSocketDisconnect
from fastapi.responses import FileResponse, HTMLResponse, JSONResponse, Response
from starlette.requests import ClientDisconnect

try:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from py_vapid import Vapid02
    from pywebpush import WebPushException, webpush
    PUSH_OK = True
except ImportError:            # 没装 pywebpush 也能跑，只是没有"关掉页面也能收到"的推送
    PUSH_OK = False

app = FastAPI()

HISTORY_SIZE = 150         # 群聊保留的最近消息条数
DM_HISTORY_SIZE = 150      # 每个私聊保留的最近消息条数
MAX_MSG_LEN = 1000         # 单条消息最大长度
MAX_NAME_LEN = 20          # 昵称最大长度
MAX_AVATAR_LEN = 200_000   # 头像（压缩后的图片）最大长度
MAX_IMAGE_MB = 15          # 单张图片上限
MAX_VIDEO_MB = 100         # 单个视频上限
MEDIA_CAP_MB = 800         # 服务器上最多保留多少图片/视频，超出后最早的会过期
MAX_CALL = 6               # 一次群通话最多几个人
MEDIA_DIR = Path(os.environ.get("MEDIA_DIR", "/tmp/chat_media"))

IMAGE_TYPES = {"image/jpeg": ".jpg", "image/png": ".png", "image/gif": ".gif", "image/webp": ".webp"}
VIDEO_TYPES = {"video/mp4": ".mp4", "video/quicktime": ".mov", "video/webm": ".webm",
               "video/3gpp": ".3gp", "video/x-m4v": ".m4v"}
EXT_TYPES = {v: k for k, v in {**IMAGE_TYPES, **VIDEO_TYPES}.items()}

# 只给正规推送服务发推送（防止有人把服务器当跳板乱发请求）
PUSH_HOSTS = ("fcm.googleapis.com", "push.services.mozilla.com", "push.apple.com",
              "notify.windows.com", "updates.push.services.mozilla.com")


def ms():
    return int(time.time() * 1000)


def now():
    return datetime.now().strftime("%H:%M")


def new_id():
    return uuid.uuid4().hex[:12]


def sysmsg(text, name=None, to=None, quiet=False):
    m = {"type": "system", "text": text, "time": now(), "ts": ms(), "id": new_id()}
    if name and to:                       # 私聊里的系统消息（比如通话记录）
        m["name"], m["to"] = name, to
    if quiet:                             # 进出群提示，不显示在聊天列表的预览里
        m["quiet"] = True
    return m


def dm_key(a, b):
    return tuple(sorted((a, b)))


# ---------------- 推送密钥 ----------------
def make_vapid():
    if not PUSH_OK:
        return None, None
    seed = os.environ.get("VAPID_SECRET") or os.environ.get("RENDER_SERVICE_ID")
    if seed:   # 由固定种子推出固定密钥，重启/重新部署后大家的订阅仍然有效
        n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
        d = int.from_bytes(hashlib.sha256(("vapid:" + seed).encode()).digest(), "big") % (n - 1) + 1
        key = ec.derive_private_key(d, ec.SECP256R1())
    else:
        key = ec.generate_private_key(ec.SECP256R1())
    pub = key.public_key().public_bytes(serialization.Encoding.X962,
                                        serialization.PublicFormat.UncompressedPoint)
    return Vapid02(private_key=key), base64.urlsafe_b64encode(pub).decode().rstrip("=")


VAPID, VAPID_PUBLIC = make_vapid()


def ice_servers():
    servers = [{"urls": ["stun:stun.cloudflare.com:3478", "stun:stun.l.google.com:19302",
                         "stun:stun.miwifi.com:3478"]}]
    turn = [u.strip() for u in os.environ.get("TURN_URLS", "").split(",") if u.strip()]
    if turn:
        servers.append({"urls": turn, "username": os.environ.get("TURN_USERNAME", ""),
                        "credential": os.environ.get("TURN_CREDENTIAL", "")})
    return servers


def send_push(endpoint, entry, payload, ttl):
    try:
        webpush(subscription_info=entry["sub"], data=json.dumps(payload, ensure_ascii=False),
                vapid_private_key=VAPID, vapid_claims={"sub": "https://" + entry["host"]},
                ttl=ttl, headers={"Urgency": "high"}, timeout=10)
    except WebPushException as e:
        code = getattr(e.response, "status_code", None)
        if code in (403, 404, 410):          # 订阅失效了，删掉
            room.subs.pop(endpoint, None)
    except Exception:
        pass


class ChatRoom:
    def __init__(self):
        self.clients: dict[WebSocket, str] = {}   # 连接 -> 昵称（同一个人可以多台设备同时在线）
        self.group: deque = deque(maxlen=HISTORY_SIZE)
        self.dms: dict[tuple, deque] = {}         # (甲, 乙) -> 两人的私聊记录
        self.avatars: dict[str, str] = {}         # 昵称 -> 头像图片(data URL)
        self.owner: dict[str, str] = {}           # 昵称 -> 设备身份码（防止别人冒用昵称看私聊）
        self.seen: dict[str, int] = {}            # 来过的所有成员 -> 最后在线时间
        self.tokens: dict[str, str] = {}          # 上传凭证 -> 昵称
        self.subs: dict[str, dict] = {}           # 推送地址 -> {sub, name, host}
        self.ws_endpoint: dict[WebSocket, str] = {}
        self.visible: dict[WebSocket, bool] = {}  # 这个人现在是不是正看着聊天页面
        self.calls: dict[str, dict] = {}          # 通话 key -> 正在进行的通话

    def online(self):
        return sorted(set(self.clients.values()))

    def is_online(self, name):
        return name in self.clients.values()

    def claim_name(self, raw, uid):
        """昵称属于第一个用它的设备；别的设备用同样的昵称会自动加编号"""
        name, i = raw, 2
        while self.owner.get(name) not in (None, uid):
            name = f"{raw}({i})"
            i += 1
        self.owner[name] = uid
        return name

    # ---------- 消息 ----------
    def box(self, m):
        if m.get("to"):
            return self.dms.setdefault(dm_key(m["name"], m["to"]), deque(maxlen=DM_HISTORY_SIZE))
        return self.group

    def all_msgs(self):
        yield from self.group
        for d in self.dms.values():
            yield from d

    def history_for(self, name):
        msgs = list(self.group)
        for k, d in self.dms.items():
            if name in k:
                msgs.extend(d)
        return sorted(msgs, key=lambda m: m["ts"])

    def remember(self, payload):
        box = self.box(payload)
        if len(box) == box.maxlen:
            drop_media(box[0])
        box.append(payload)
        if payload.get("url"):
            items = sorted((m for m in self.all_msgs() if m.get("url") and not m.get("expired")),
                           key=lambda m: m["ts"])
            total = sum(m.get("size", 0) for m in items)
            for m in items:
                if total <= MEDIA_CAP_MB * 1024 * 1024:
                    break
                total -= m.get("size", 0)
                drop_media(m)

    async def broadcast_text(self, text):
        dead = []
        for ws in list(self.clients):
            try:
                await ws.send_text(text)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self.clients.pop(ws, None)

    async def broadcast(self, payload: dict, save=True):
        if save:
            self.remember(payload)
        await self.broadcast_text(json.dumps(payload, ensure_ascii=False))

    async def send_to(self, name, payload):
        text = payload if isinstance(payload, str) else json.dumps(payload, ensure_ascii=False)
        for ws, n in list(self.clients.items()):
            if n == name:
                try:
                    await ws.send_text(text)
                except Exception:
                    pass

    async def deliver(self, payload):
        """保存消息，并只发给该看到的人：群消息发给所有人，私聊只发给两个人"""
        if not payload.get("to"):
            await self.broadcast(payload)
            return
        self.remember(payload)
        text = json.dumps(payload, ensure_ascii=False)
        await self.send_to(payload["name"], text)
        if payload["to"] != payload["name"]:
            await self.send_to(payload["to"], text)

    async def send_users(self):
        await self.broadcast({"type": "users", "users": self.online(), "members": sorted(self.seen)}, save=False)

    async def send_avatars(self):
        await self.broadcast({"type": "avatars", "avatars": self.avatars}, save=False)

    # ---------- 推送 ----------
    def add_sub(self, ws, name, sub, host):
        if not PUSH_OK or not isinstance(sub, dict):
            return
        ep, keys = sub.get("endpoint"), sub.get("keys") or {}
        if not (isinstance(ep, str) and len(ep) < 1000 and isinstance(keys, dict)
                and isinstance(keys.get("p256dh"), str) and isinstance(keys.get("auth"), str)):
            return
        u = urlparse(ep)
        if u.scheme != "https" or not any(u.hostname == h or (u.hostname or "").endswith("." + h)
                                          for h in PUSH_HOSTS):
            return
        self.subs[ep] = {"sub": {"endpoint": ep, "keys": {"p256dh": keys["p256dh"], "auth": keys["auth"]}},
                         "name": name, "host": host or "localhost"}
        self.ws_endpoint[ws] = ep

    def push(self, payload, exclude=None, only=None, ttl=86400):
        """给不在看聊天页面的人发系统通知（锁屏、后台都能收到）。only=只发给这个人"""
        if not PUSH_OK or not self.subs:
            return
        watching = {self.ws_endpoint.get(w) for w, v in self.visible.items() if v and w in self.clients}
        for ep, entry in list(self.subs.items()):
            if entry["name"] == exclude or ep in watching:
                continue
            if only is not None and entry["name"] != only:
                continue
            asyncio.get_running_loop().run_in_executor(None, send_push, ep, entry, payload, ttl)

    def push_msg(self, msg):
        body = preview(msg)
        if msg.get("to"):
            self.push({"title": msg["name"], "body": body, "tag": "m-" + msg["id"], "kind": "msg",
                       "conv": "dm:" + msg["name"]}, only=msg["to"])
        else:
            self.push({"title": "群聊", "body": f"{msg['name']}: {body}", "tag": "m-" + msg["id"], "kind": "msg",
                       "conv": "group"}, exclude=msg["name"])

    # ---------- 通话 ----------
    @staticmethod
    def call_key(name, to):
        return "dm:" + "\n".join(dm_key(name, to)) if to else "group"

    def call_of(self, name):
        for c in self.calls.values():
            if name in c["members"]:
                return c
        return None

    @staticmethod
    def call_public(c, ended=False):
        return {"media": c["media"], "members": c["members"], "by": c["by"], "start": c["start"],
                "invite": c["invite"], "ended": ended}

    def calls_for(self, name):
        return [self.call_public(c) for c in self.calls.values() if not c["invite"] or name in c["invite"]]

    async def send_call(self, c, ended=False):
        text = json.dumps({"type": "call_state", "call": self.call_public(c, ended)}, ensure_ascii=False)
        if c["invite"]:
            for n in c["invite"]:
                await self.send_to(n, text)
        else:
            await self.broadcast_text(text)

    async def call_note(self, c, text):
        if c["invite"]:
            other = next((n for n in c["invite"] if n != c["by"]), c["by"])
            await self.deliver(sysmsg(text, name=c["by"], to=other))
        else:
            await self.deliver(sysmsg(text))

    async def leave_call(self, name):
        c = self.call_of(name)
        if not c:
            return
        c["members"].remove(name)
        if not c["members"]:
            self.calls.pop(c["key"], None)
            if c.get("talk_at"):
                secs = int(time.time() - c["talk_at"])
                await self.call_note(c, f"通话结束，时长 {secs // 60:02d}:{secs % 60:02d}")
            else:
                await self.call_note(c, "通话已取消")
            await self.send_call(c, ended=True)
        else:
            await self.send_call(c)


room = ChatRoom()


def drop_media(m):
    """删除过期的图片/视频文件"""
    url = m.get("url")
    if url and not m.get("expired"):
        try:
            (MEDIA_DIR / url.rsplit("/", 1)[-1]).unlink(missing_ok=True)
        except Exception:
            pass
        m["expired"] = True


def valid_avatar(a) -> bool:
    return isinstance(a, str) and a.startswith("data:image/") and len(a) <= MAX_AVATAR_LEN


def preview(m):
    return {"image": "[图片]", "video": "[视频]"}.get(m["type"]) or m.get("text", "")[:120]


def valid_to(name, to):
    """私聊对象必须是来过群里的其他成员"""
    return isinstance(to, str) and to != name and to in room.seen


async def toast(ws, text):
    await ws.send_text(json.dumps({"type": "toast", "text": text}, ensure_ascii=False))


async def handle_call(ws, name, kind, data):
    to = data.get("to") or None
    if to is not None and not valid_to(name, to):
        return
    key = room.call_key(name, to)
    c = room.calls.get(key)
    if kind == "call_decline":
        if c:
            for m in list(c["members"]):
                await room.send_to(m, {"type": "call_declined", "name": name})
        return
    if kind == "call_leave":
        await room.leave_call(name)
        return
    # call_start / call_join
    mine = room.call_of(name)
    if mine and mine is not c:
        await toast(ws, "你已经在另一个通话里了")
        return
    if not c:
        if kind != "call_start":
            await ws.send_text(json.dumps({"type": "call_state", "call": {
                "media": "video", "members": [], "by": "", "start": 0,
                "invite": sorted((name, to)) if to else None, "ended": True}}))
            return
        media = "audio" if data.get("media") == "audio" else "video"
        label = "视频" if media == "video" else "语音"
        c = room.calls[key] = {"key": key, "media": media, "members": [], "by": name, "start": ms(),
                               "talk_at": None, "invite": list(dm_key(name, to)) if to else None}
        if to:
            await room.call_note(c, f"{name} 发起了{label}通话")
            room.push({"title": name, "body": f"邀请你{label}通话", "tag": f"call-{c['start']}", "kind": "call",
                       "conv": "dm:" + name}, only=to, ttl=60)
        else:
            await room.call_note(c, f"{name} 发起了群{label}通话")
            room.push({"title": name, "body": f"邀请你加入群{label}通话", "tag": f"call-{c['start']}",
                       "kind": "call", "conv": "group"}, exclude=name, ttl=60)
    if name in c["members"]:
        return
    limit = 2 if c["invite"] else MAX_CALL
    if len(c["members"]) >= limit:
        await toast(ws, "通话人数已满")
        return
    peers = list(c["members"])
    c["members"].append(name)
    if len(c["members"]) >= 2 and not c["talk_at"]:
        c["talk_at"] = time.time()
    await ws.send_text(json.dumps({"type": "call_joined", "peers": peers, "media": c["media"]}))
    await room.send_call(c)


@app.websocket("/ws")
async def websocket_endpoint(ws: WebSocket):
    await ws.accept()
    name = None
    host = ws.headers.get("host", "")
    try:
        # 第一条消息必须是 {"type": "join", "name": "...", "uid": "..."}
        first = json.loads(await ws.receive_text())
        raw = re.sub(r"[\x00-\x1f\x7f]", "", str(first.get("name", ""))).strip()[:MAX_NAME_LEN] or "匿名"
        uid = str(first.get("uid") or "")[:64] or secrets.token_hex(12)
        name = room.claim_name(raw, uid)
        if valid_avatar(first.get("avatar")):
            room.avatars[name] = first["avatar"]
        token = secrets.token_urlsafe(18)
        room.tokens[token] = name
        first_device = not room.is_online(name)
        room.seen[name] = ms()

        # 先把历史记录（群聊 + 自己的私聊）和最终昵称发给新用户
        await ws.send_text(json.dumps({
            "type": "welcome", "name": name, "history": room.history_for(name), "avatars": room.avatars,
            "token": token, "vapid": VAPID_PUBLIC, "ice": ice_servers(), "calls": room.calls_for(name),
            "limits": {"image_mb": MAX_IMAGE_MB, "video_mb": MAX_VIDEO_MB},
        }, ensure_ascii=False))

        room.clients[ws] = name
        room.visible[ws] = bool(first.get("visible", True))
        if first_device:
            await room.broadcast(sysmsg(f"{name} 加入了聊天室", quiet=True))
        await room.send_users()
        await room.send_avatars()

        while True:
            data = json.loads(await ws.receive_text())
            if not isinstance(data, dict):
                continue
            kind = data.get("type")
            if kind == "avatar":
                if valid_avatar(data.get("avatar")):
                    room.avatars[name] = data["avatar"]
                elif data.get("avatar") is None:
                    room.avatars.pop(name, None)
                await room.send_avatars()
            elif kind == "vis":
                room.visible[ws] = bool(data.get("visible"))
            elif kind == "push_sub":
                room.add_sub(ws, name, data.get("sub"), host)
            elif kind in ("call_start", "call_join", "call_leave", "call_decline"):
                await handle_call(ws, name, kind, data)
            elif kind == "signal":           # 通话建立连接用的数据，原样转给对方
                to, payload = data.get("to"), data.get("data")
                c = room.call_of(name)
                if c and isinstance(to, str) and to in c["members"] and isinstance(payload, dict):
                    text = json.dumps({"type": "signal", "from": name, "data": payload}, ensure_ascii=False)
                    if len(text) < 100_000:
                        await room.send_to(to, text)
            else:
                text = str(data.get("text", "")).strip()[:MAX_MSG_LEN]
                to = data.get("to") or None
                if to is not None and not valid_to(name, to):
                    continue
                if text:
                    msg = {"type": "chat", "name": name, "text": text, "time": now(), "ts": ms(), "id": new_id()}
                    if to:
                        msg["to"] = to
                    await room.deliver(msg)
                    room.push_msg(msg)

    except (WebSocketDisconnect, json.JSONDecodeError):
        pass
    finally:
        room.visible.pop(ws, None)
        room.ws_endpoint.pop(ws, None)
        if ws in room.clients:
            room.clients.pop(ws)
            if not room.is_online(name):
                room.seen[name] = ms()
                await room.leave_call(name)
                await room.broadcast(sysmsg(f"{name} 离开了聊天室", quiet=True))
            await room.send_users()


@app.post("/upload")
async def upload(request: Request, token: str = "", kind: str = "", cid: str = "", to: str = "",
                 w: int = 0, h: int = 0, dur: int = 0):
    name = room.tokens.get(token)
    if not name:
        return JSONResponse({"error": "请刷新页面后重试"}, status_code=403)
    if to and not valid_to(name, to):
        return JSONResponse({"error": "找不到这个人"}, status_code=400)
    types = IMAGE_TYPES if kind == "image" else VIDEO_TYPES if kind == "video" else None
    ctype = request.headers.get("content-type", "").split(";")[0].strip().lower()
    if not types or ctype not in types:
        return JSONResponse({"error": "不支持这种文件"}, status_code=415)
    limit = (MAX_IMAGE_MB if kind == "image" else MAX_VIDEO_MB) * 1024 * 1024
    if int(request.headers.get("content-length") or 0) > limit:
        return JSONResponse({"error": "文件太大"}, status_code=413)

    fname = uuid.uuid4().hex + types[ctype]
    path = MEDIA_DIR / fname
    size = 0
    try:
        with open(path, "wb") as f:
            async for chunk in request.stream():
                size += len(chunk)
                if size > limit:
                    raise ValueError
                f.write(chunk)
    except ValueError:
        path.unlink(missing_ok=True)
        return JSONResponse({"error": "文件太大"}, status_code=413)
    except ClientDisconnect:
        path.unlink(missing_ok=True)
        return Response(status_code=400)
    if size == 0:
        path.unlink(missing_ok=True)
        return JSONResponse({"error": "空文件"}, status_code=400)

    clamp = lambda v: max(0, min(int(v), 20000))
    msg = {"type": kind, "name": name, "url": f"/media/{fname}", "w": clamp(w), "h": clamp(h),
           "size": size, "time": now(), "ts": ms(), "id": new_id()}
    if to:
        msg["to"] = to
    if dur:
        msg["dur"] = clamp(dur)
    if cid:
        msg["cid"] = cid[:40]
    await room.deliver(msg)
    room.push_msg(msg)
    return {"ok": True}


@app.get("/media/{fname}")
async def media(fname: str):
    if not re.fullmatch(r"[0-9a-f]{32}\.[a-z0-9]{2,4}", fname):
        return Response(status_code=404)
    path = MEDIA_DIR / fname
    if not path.is_file():
        return Response("这个文件已过期", status_code=404)
    return FileResponse(path, media_type=EXT_TYPES.get(path.suffix, "application/octet-stream"),
                        headers={"Cache-Control": "private, max-age=31536000, immutable"})


@app.get("/")
async def index():
    return HTMLResponse(PAGE, headers={"Cache-Control": "no-cache"})


@app.get("/sw.js")
async def service_worker():
    return Response(SW_JS, media_type="application/javascript", headers={"Cache-Control": "no-cache"})


@app.get("/manifest.webmanifest")
async def manifest():
    return JSONResponse({
        "name": "群聊", "short_name": "群聊", "start_url": "/", "scope": "/", "display": "standalone",
        "background_color": "#ededed", "theme_color": "#ededed",
        "icons": [{"src": "/icon-192.png", "sizes": "192x192", "type": "image/png"},
                  {"src": "/icon-512.png", "sizes": "512x512", "type": "image/png"}],
    }, media_type="application/manifest+json")


@app.get("/icon-{size}.png")
async def icon(size: int):
    data = {192: ICON_192, 512: ICON_512}.get(size)
    if not data:
        return Response(status_code=404)
    return Response(base64.b64decode(data), media_type="image/png",
                    headers={"Cache-Control": "public, max-age=86400"})


@app.get("/healthz")
async def healthz():
    return {"ok": True}


@app.on_event("startup")
async def startup():
    shutil.rmtree(MEDIA_DIR, ignore_errors=True)
    MEDIA_DIR.mkdir(parents=True, exist_ok=True)
    url = os.environ.get("RENDER_EXTERNAL_URL")
    if url and os.environ.get("KEEP_AWAKE", "1") != "0":
        asyncio.get_running_loop().create_task(keep_awake(url.rstrip("/") + "/healthz"))


async def keep_awake(url):
    """Render 免费实例 15 分钟没人访问就会睡着，睡着就收不到消息推送；每 10 分钟访问一下自己"""
    while True:
        await asyncio.sleep(600)
        try:
            await asyncio.to_thread(lambda: urllib.request.urlopen(url, timeout=20).read())
        except Exception:
            pass


SW_JS = r"""
self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", e => e.waitUntil(self.clients.claim()));
self.addEventListener("push", e => {
  let d = {};
  try { d = e.data ? e.data.json() : {}; } catch (_) { d = { body: e.data ? e.data.text() : "" }; }
  const call = d.kind === "call";
  e.waitUntil(self.registration.showNotification(d.title || "群聊", {
    body: d.body || "有新消息", tag: d.tag || "chat", renotify: true,
    icon: "/icon-192.png", badge: "/icon-192.png", requireInteraction: call,
    vibrate: call ? [500, 250, 500, 250, 500] : [200, 100, 200], data: { conv: d.conv || "" }
  }));
});
self.addEventListener("notificationclick", e => {
  e.notification.close();
  const conv = (e.notification.data && e.notification.data.conv) || "";
  e.waitUntil((async () => {
    const list = await self.clients.matchAll({ type: "window", includeUncontrolled: true });
    for (const c of list) {
      if ("focus" in c) { await c.focus(); if (conv) c.postMessage({ open: conv }); return; }
    }
    return self.clients.openWindow("/" + (conv ? "#c=" + encodeURIComponent(conv) : ""));
  })());
});
"""


PAGE = r"""<!doctype html>
<html lang="zh">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<title>群聊</title>
<link rel="manifest" href="/manifest.webmanifest">
<link rel="apple-touch-icon" href="/icon-192.png">
<link rel="icon" href="/icon-192.png">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="群聊">
<meta name="apple-mobile-web-app-status-bar-style" content="default">
<meta name="theme-color" content="#ededed">
<style>
  :root { --bg:#ededed; --bar:#ededed; --input-bar:#f7f7f7; --field:#fff; --fg:#191919; --muted:#8a8a8a; --line:#d9d9d9;
          --other:#fff; --me:#95ec69; --me-fg:#191919; --green:#07c160; --green-press:#06ad56; --red:#fa5151;
          --tip:#fdf6e3; --tip-fg:#8a6d1f; --callbar:#e7f7ee; --callbar-fg:#06964b; --row-press:#ececec; }
  @media (prefers-color-scheme: dark) {
    :root { --bg:#111; --bar:#191919; --input-bar:#1e1e1e; --field:#2c2c2c; --fg:#e5e5e5; --muted:#7d7d7d; --line:#2a2a2a;
            --other:#2c2c2c; --me:#3eb575; --me-fg:#0d0d0d; --tip:#2b2614; --tip-fg:#d9bf72; --callbar:#13281d; --callbar-fg:#4cd38b;
            --row-press:#262626; color-scheme:dark; }
  }
  * { box-sizing:border-box; -webkit-tap-highlight-color:transparent; }
  html, body { height:100%; margin:0; }
  body { background:var(--bg); color:var(--fg); font-family:-apple-system,BlinkMacSystemFont,"PingFang SC","Hiragino Sans GB","Microsoft YaHei",sans-serif; font-size:16px; }
  button { font:inherit; }
  svg.i { width:24px; height:24px; fill:none; stroke:currentColor; stroke-width:1.7; stroke-linecap:round; stroke-linejoin:round; }
  .app { height:100%; max-width:760px; margin:0 auto; }
  .view { height:100%; display:flex; flex-direction:column; }
  header { flex:none; height:48px; display:flex; align-items:center; justify-content:center; position:relative;
           background:var(--bar); border-bottom:.5px solid var(--line); padding-top:env(safe-area-inset-top,0px); box-sizing:content-box; }
  header h1 { margin:0; font-size:17px; font-weight:600; max-width:60%; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  header h1 .cnt { font-weight:400; }
  .status { font-size:12px; color:var(--muted); font-weight:400; margin-left:6px; }
  .hbtn { position:absolute; bottom:6px; background:none; border:none; color:var(--fg); font-size:14px; padding:6px 8px; border-radius:6px; cursor:pointer; display:flex; align-items:center; gap:2px; }
  .hbtn:hover { background:var(--line); }
  .hbtn.left { left:6px; }  .hbtn.right { right:8px; }
  #soundBtn svg.i { width:22px; height:22px; }
  #back svg.i { width:22px; height:22px; stroke-width:2; }
  #back .ub { font-size:13px; color:var(--muted); }
  .strip { flex:none; display:flex; align-items:center; gap:10px; padding:8px 12px; font-size:13px; line-height:1.4; }
  #alertBar { background:var(--tip); color:var(--tip-fg); }
  #alertBar .t { flex:1; }
  #alertBar button { border:none; border-radius:5px; cursor:pointer; }
  #alertOn { background:var(--green); color:#fff; padding:5px 12px; font-size:13px; }
  #alertX { background:none; color:inherit; font-size:18px; padding:0 4px; line-height:1; }
  #callBar { background:var(--callbar); color:var(--callbar-fg); cursor:pointer; justify-content:center; font-weight:500; }

  /* ---------- 聊天列表 ---------- */
  #convList { flex:1; overflow-y:auto; background:var(--field); }
  .conv { display:flex; align-items:center; gap:12px; padding:12px 16px; cursor:pointer; position:relative; }
  .conv:active { background:var(--row-press); }
  .conv + .conv::before { content:""; position:absolute; top:0; left:72px; right:0; border-top:.5px solid var(--line); }
  .conv .av { position:relative; flex:none; }
  .conv .avatar { width:44px; height:44px; font-size:18px; }
  .badge { position:absolute; top:-6px; right:-7px; min-width:18px; height:18px; padding:0 5px; border-radius:9px; background:var(--red); color:#fff;
           font-size:11px; line-height:18px; text-align:center; font-weight:500; font-variant-numeric:tabular-nums; }
  .dot { position:absolute; right:-2px; bottom:-2px; width:12px; height:12px; border-radius:50%; background:var(--green); border:2px solid var(--field); }
  .cmain { flex:1; min-width:0; display:flex; flex-direction:column; gap:3px; }
  .ctop { display:flex; align-items:baseline; gap:8px; }
  .ctitle { flex:1; min-width:0; font-size:16px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .ctime { flex:none; font-size:12px; color:var(--muted); font-variant-numeric:tabular-nums; }
  .cprev { font-size:13px; color:var(--muted); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .cprev .live { color:var(--green); }
  .gav { background:var(--green); }
  .gav svg.i { width:26px; height:26px; stroke:#fff; stroke-width:1.8; }

  /* ---------- 聊天窗口 ---------- */
  #list { flex:1; overflow-y:auto; padding:12px; display:flex; flex-direction:column; gap:16px; }
  .time { align-self:center; font-size:12px; color:var(--muted); }
  .sys { align-self:center; font-size:12px; color:var(--muted); background:rgba(0,0,0,.06); padding:3px 8px; border-radius:4px; text-align:center; }
  .msg { display:flex; gap:10px; align-items:flex-start; }
  .msg.me { flex-direction:row-reverse; }
  .avatar { flex:none; width:40px; height:40px; border-radius:5px; color:#fff; font-size:16px; font-weight:600;
            display:flex; align-items:center; justify-content:center; }
  .body { display:flex; flex-direction:column; min-width:0; max-width:calc(100% - 110px); }
  .msg.me .body { align-items:flex-end; }
  .name { font-size:12px; color:var(--muted); margin:0 0 4px 2px; }
  .msg.me .name, #list.dm .name { display:none; }
  .msg .avatar { cursor:pointer; }
  .bubble { position:relative; background:var(--other); padding:9px 12px; border-radius:5px; line-height:1.45;
            white-space:pre-wrap; word-break:break-word; overflow-wrap:anywhere; }
  .bubble::before { content:""; position:absolute; top:13px; left:-5px; width:10px; height:10px; background:inherit; transform:rotate(45deg); }
  .msg.me .bubble { background:var(--me); color:var(--me-fg); }
  .msg.me .bubble::before { left:auto; right:-5px; }
  .bubble.gone { color:var(--muted); }
  .media { position:relative; border-radius:6px; overflow:hidden; background:var(--line); max-width:100%; }
  .media img { display:block; width:100%; height:100%; object-fit:cover; cursor:zoom-in; }
  .media video { display:block; width:100%; height:100%; object-fit:contain; background:#000; }
  .media .up { position:absolute; inset:0; display:flex; align-items:center; justify-content:center; background:rgba(0,0,0,.45); color:#fff; font-size:14px; text-align:center; padding:6px; }
  .media .up.err { background:rgba(0,0,0,.6); color:#ff8d8d; cursor:pointer; }
  footer { flex:none; display:flex; gap:8px; align-items:flex-end; background:var(--input-bar); border-top:.5px solid var(--line);
           padding:8px 12px calc(8px + env(safe-area-inset-bottom,0px)); }
  footer.open { padding-bottom:8px; }
  #text { flex:1; min-width:0; resize:none; border:none; outline:none; border-radius:5px; background:var(--field); color:var(--fg);
          font:inherit; line-height:1.4; padding:8px 10px; height:38px; max-height:120px; }
  #plus { flex:none; width:38px; height:38px; border:none; background:none; color:var(--fg); cursor:pointer; padding:0; display:flex; align-items:center; justify-content:center; }
  #plus svg.i { width:30px; height:30px; stroke-width:1.4; transition:transform .15s; }
  footer.open #plus svg.i { transform:rotate(45deg); }
  #send { flex:none; height:38px; padding:0 16px; border:none; border-radius:5px; background:var(--green); color:#fff; font-size:15px; cursor:pointer; }
  #send:hover { background:var(--green-press); }
  #more { flex:none; display:grid; grid-template-columns:repeat(4,1fr); gap:18px 8px; padding:18px 16px calc(18px + env(safe-area-inset-bottom,0px));
          background:var(--input-bar); border-top:.5px solid var(--line); }
  #more button { background:none; border:none; color:var(--muted); font-size:12px; cursor:pointer; display:flex; flex-direction:column; align-items:center; gap:7px; }
  #more .ic { width:58px; height:58px; border-radius:14px; background:var(--field); color:var(--fg); display:flex; align-items:center; justify-content:center; }
  #more .ic svg.i { width:28px; height:28px; }

  /* ---------- 资料弹窗 ---------- */
  .sheet-wrap { position:fixed; inset:0; background:rgba(0,0,0,.45); display:flex; align-items:center; justify-content:center; padding:16px; z-index:20; }
  .sheet { background:var(--bar); border-radius:12px; width:min(100%,320px); padding:20px; display:flex; flex-direction:column; gap:14px; }
  .sheet h2 { margin:0; font-size:17px; text-align:center; }
  #nick { border:none; outline:none; border-radius:6px; background:var(--field); color:var(--fg); font:inherit; padding:10px 12px; }
  #join { height:40px; border:none; border-radius:6px; background:var(--green); color:#fff; cursor:pointer; }
  img.avatar { object-fit:cover; background:var(--line); }
  .pick { display:flex; flex-direction:column; align-items:center; gap:8px; }
  #preview { width:72px; height:72px; border-radius:8px; font-size:28px; }
  .links { display:flex; gap:16px; }
  .links button, #loginLink { background:none; border:none; color:var(--green); font-size:14px; cursor:pointer; padding:4px; }
  #loginLink { font-size:13px; align-self:center; }
  .row2 { display:flex; gap:10px; }
  .row2 button { flex:1; }
  #cancel { height:40px; border:none; border-radius:6px; background:var(--field); color:var(--fg); cursor:pointer; }
  #toast { position:fixed; left:50%; top:40%; transform:translate(-50%,-50%); background:rgba(0,0,0,.78); color:#fff; padding:10px 16px;
           border-radius:8px; font-size:14px; z-index:60; max-width:80vw; text-align:center; pointer-events:none; }
  #viewer { position:fixed; inset:0; background:#000; z-index:50; display:flex; align-items:center; justify-content:center; cursor:zoom-out; }
  #viewer img { max-width:100%; max-height:100%; object-fit:contain; }

  /* ---------- 通话 ---------- */
  .overlay { position:fixed; inset:0; z-index:40; background:#141414; color:#fff; }
  #ring { display:flex; flex-direction:column; align-items:center; justify-content:space-between;
          padding:calc(70px + env(safe-area-inset-top,0px)) 24px calc(60px + env(safe-area-inset-bottom,0px)); }
  .ring-who { display:flex; flex-direction:column; align-items:center; gap:14px; text-align:center; }
  .avatar.big { width:96px; height:96px; border-radius:12px; font-size:40px; }
  #ringName { font-size:24px; font-weight:600; }
  #ringText { font-size:15px; color:#bbb; }
  .cbtns { display:flex; justify-content:center; gap:44px; width:100%; }
  .cbtn { display:flex; flex-direction:column; align-items:center; gap:8px; font-size:12px; color:#ddd; background:none; border:none; cursor:pointer; padding:0; }
  .cbtn .round { width:64px; height:64px; border-radius:50%; background:rgba(255,255,255,.18); color:#fff; display:flex; align-items:center; justify-content:center; }
  .cbtn .round svg.i { width:28px; height:28px; }
  .cbtn.on .round { background:#fff; color:#111; }
  .cbtn.red .round { background:var(--red); }  .cbtn.green .round { background:var(--green); }
  .cbtn.red svg.i { transform:rotate(135deg); }
  #tiles { position:absolute; inset:0; display:grid; gap:2px; grid-auto-rows:1fr; }
  #tiles.n2 { grid-template-rows:1fr 1fr; }
  #tiles.n3, #tiles.n4 { grid-template-columns:1fr 1fr; }
  #tiles.n5, #tiles.n6 { grid-template-columns:1fr 1fr; grid-template-rows:repeat(3,1fr); }
  @media (orientation:landscape) { #tiles.n2 { grid-template-rows:none; grid-template-columns:1fr 1fr; } }
  .tile { position:relative; background:#222; overflow:hidden; display:flex; flex-direction:column; align-items:center; justify-content:center; gap:10px; }
  .tile video { position:absolute; inset:0; width:100%; height:100%; object-fit:cover; display:none; background:#000; }
  .tile.has-video:not(.cam-off) video { display:block; }
  .tile audio { display:none; }
  .tlabel { position:absolute; left:10px; bottom:8px; font-size:13px; text-shadow:0 1px 3px rgba(0,0,0,.8); z-index:1; }
  .tile .tstate { font-size:13px; color:#bbb; z-index:1; }
  .tile.has-video:not(.cam-off) .tstate:empty { display:none; }
  #localVid { position:absolute; right:12px; top:calc(56px + env(safe-area-inset-top,0px)); width:28vw; max-width:150px; aspect-ratio:3/4;
              object-fit:cover; border-radius:8px; background:#000; z-index:2; box-shadow:0 2px 10px rgba(0,0,0,.5); }
  #localVid.mirror { transform:scaleX(-1); }
  #callView.solo #localVid { inset:0; top:0; right:0; width:100%; height:100%; max-width:none; aspect-ratio:auto; border-radius:0; box-shadow:none; }
  #callTop { position:absolute; left:0; right:0; top:0; padding:calc(14px + env(safe-area-inset-top,0px)) 16px 30px; text-align:center; z-index:3;
             background:linear-gradient(rgba(0,0,0,.55),transparent); font-size:15px; pointer-events:none; }
  #callTime { display:block; font-size:13px; color:#ccc; margin-top:3px; }
  #callBtns { position:absolute; left:0; right:0; bottom:0; z-index:3; padding:36px 12px calc(28px + env(safe-area-inset-bottom,0px));
              background:linear-gradient(transparent,rgba(0,0,0,.6)); gap:22px; }
  [hidden] { display:none !important; }
</style>
</head>
<body>
<svg width="0" height="0" style="position:absolute">
  <symbol id="i-bell" viewBox="0 0 24 24"><path d="M6 16v-5a6 6 0 0112 0v5l1.5 2h-15z"/><path d="M10 20.5a2 2 0 004 0"/></symbol>
  <symbol id="i-bell-off" viewBox="0 0 24 24"><path d="M6 16v-5a6 6 0 0112 0v5l1.5 2h-15z"/><path d="M10 20.5a2 2 0 004 0"/><path d="M4 4l16 16"/></symbol>
  <symbol id="i-back" viewBox="0 0 24 24"><path d="M15 4.5L7.5 12l7.5 7.5"/></symbol>
  <symbol id="i-group" viewBox="0 0 24 24"><circle cx="9" cy="8.5" r="3.2"/><path d="M3 19.5c.6-3.4 3-5.3 6-5.3s5.4 1.9 6 5.3"/><path d="M15.5 5.6a3 3 0 010 5.8M17.6 14.6c1.8.7 3 2.4 3.4 4.9"/></symbol>
  <symbol id="i-plus" viewBox="0 0 24 24"><circle cx="12" cy="12" r="9.5"/><path d="M12 7.5v9M7.5 12h9"/></symbol>
  <symbol id="i-image" viewBox="0 0 24 24"><rect x="3" y="5" width="18" height="14" rx="2"/><circle cx="9" cy="10" r="1.6"/><path d="M4 17l5-5 4 4 3-3 4 4"/></symbol>
  <symbol id="i-camera" viewBox="0 0 24 24"><path d="M4 8h3l2-2.5h6L17 8h3v11H4z"/><circle cx="12" cy="13" r="3.5"/></symbol>
  <symbol id="i-record" viewBox="0 0 24 24"><circle cx="12" cy="12" r="8.5"/><circle cx="12" cy="12" r="3.5" fill="currentColor"/></symbol>
  <symbol id="i-video" viewBox="0 0 24 24"><rect x="3" y="6.5" width="12.5" height="11" rx="2"/><path d="M15.5 10.5l5-3v9l-5-3z"/></symbol>
  <symbol id="i-video-off" viewBox="0 0 24 24"><rect x="3" y="6.5" width="12.5" height="11" rx="2"/><path d="M15.5 10.5l5-3v9l-5-3z"/><path d="M3 4l17 17"/></symbol>
  <symbol id="i-phone" viewBox="0 0 24 24"><path d="M6.6 3.5h3l1.5 4-2 1.3a11 11 0 005.1 5.1l1.3-2 4 1.5v3a2 2 0 01-2.2 2A16.5 16.5 0 014.6 5.7a2 2 0 012-2.2z"/></symbol>
  <symbol id="i-mic" viewBox="0 0 24 24"><rect x="9" y="3" width="6" height="11" rx="3"/><path d="M5.5 11a6.5 6.5 0 0013 0M12 17.5V21"/></symbol>
  <symbol id="i-mic-off" viewBox="0 0 24 24"><rect x="9" y="3" width="6" height="11" rx="3"/><path d="M5.5 11a6.5 6.5 0 0013 0M12 17.5V21M4 4l16 16"/></symbol>
  <symbol id="i-flip" viewBox="0 0 24 24"><path d="M4 8h3l2-2.5h6L17 8h3v11H4z"/><path d="M9.2 12.2a3 3 0 015.3-1.4M14.8 13.8a3 3 0 01-5.3 1.4"/><path d="M14.8 9v2h-2M9.2 17v-2h2"/></symbol>
</svg>

<div class="app">
  <section id="home" class="view">
    <header>
      <button id="soundBtn" class="hbtn left" hidden aria-label="提示音"><svg class="i"><use href="#i-bell"/></svg></button>
      <h1>消息<span class="status"></span></h1>
      <button id="profileBtn" class="hbtn right" hidden>资料</button>
    </header>
    <div id="alertBar" class="strip" hidden><span class="t"></span><button id="alertOn" hidden>开启</button><button id="alertX" aria-label="关闭">×</button></div>
    <div id="convList"></div>
  </section>

  <section id="chat" class="view" hidden>
    <header>
      <button id="back" class="hbtn left" aria-label="返回"><svg class="i"><use href="#i-back"/></svg><span class="ub"></span></button>
      <h1><span id="chatTitle"></span><span class="cnt" id="chatCount"></span><span class="status"></span></h1>
    </header>
    <div id="callBar" class="strip" hidden></div>
    <main id="list"></main>
    <footer id="foot">
      <textarea id="text" rows="1" placeholder="发消息" maxlength="1000"></textarea>
      <button id="plus" aria-label="更多"><svg class="i"><use href="#i-plus"/></svg></button>
      <button id="send" hidden>发送</button>
    </footer>
    <div id="more" hidden>
      <button data-act="album"><span class="ic"><svg class="i"><use href="#i-image"/></svg></span>照片/视频</button>
      <button data-act="photo"><span class="ic"><svg class="i"><use href="#i-camera"/></svg></span>拍照</button>
      <button data-act="record"><span class="ic"><svg class="i"><use href="#i-record"/></svg></span>录像</button>
      <button data-act="vcall"><span class="ic"><svg class="i"><use href="#i-video"/></svg></span>视频通话</button>
      <button data-act="acall"><span class="ic"><svg class="i"><use href="#i-phone"/></svg></span>语音通话</button>
    </div>
  </section>
  <input type="file" id="pickAlbum" accept="image/*,video/*" multiple hidden>
  <input type="file" id="pickPhoto" accept="image/*" capture="environment" hidden>
  <input type="file" id="pickVideo" accept="video/*" capture="environment" hidden>
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
    <input id="nick" maxlength="20" placeholder="昵称，比如：爸爸、加加" autofocus>
    <div class="row2">
      <button id="cancel" type="button" hidden>取消</button>
      <button id="join" type="button">进入</button>
    </div>
    <button id="loginLink" type="button" hidden>在另一台手机/电脑上登录我的账号</button>
  </div>
</div>

<div id="ring" class="overlay" hidden>
  <div class="ring-who"><div id="ringAv"></div><div id="ringName"></div><div id="ringText"></div></div>
  <div class="cbtns">
    <button id="decline" class="cbtn red"><span class="round"><svg class="i"><use href="#i-phone"/></svg></span>拒绝</button>
    <button id="accept" class="cbtn green"><span class="round"><svg class="i"><use href="#i-phone"/></svg></span>接听</button>
  </div>
</div>

<div id="callView" class="overlay" hidden>
  <div id="tiles"></div>
  <video id="localVid" autoplay playsinline muted hidden></video>
  <div id="callTop"><span id="callTitle"></span><span id="callTime"></span></div>
  <div id="callBtns" class="cbtns">
    <button id="btnMic" class="cbtn"><span class="round"><svg class="i"><use href="#i-mic"/></svg></span><span>静音</span></button>
    <button id="btnCam" class="cbtn"><span class="round"><svg class="i"><use href="#i-video"/></svg></span><span>关摄像头</span></button>
    <button id="btnFlip" class="cbtn" hidden><span class="round"><svg class="i"><use href="#i-flip"/></svg></span><span>翻转</span></button>
    <button id="btnHang" class="cbtn red"><span class="round"><svg class="i"><use href="#i-phone"/></svg></span><span>挂断</span></button>
  </div>
</div>

<div id="viewer" hidden><img alt=""></div>
<div id="toast" hidden></div>

<script>
const $ = id => document.getElementById(id);
const list = $("list"), textEl = $("text"), sendBtn = $("send");
let ws, myName = "", joined = false, token = "", vapidKey = null, iceServers = [], limits = { image_mb:15, video_mb:100 };
let avatars = {}, users = [], members = [];
let myAvatar = null, draftAvatar = null, soundOn = true, uid = "";
let pushActive = false, swReg = null, pendingOpen = null;
const ls = {
  get(k) { try { return localStorage.getItem(k); } catch (e) { return null; } },
  set(k, v) { try { v == null ? localStorage.removeItem(k) : localStorage.setItem(k, v); } catch (e) {} }
};
myAvatar = ls.get("chatAvatar"); soundOn = ls.get("chatSound") !== "0";
uid = ls.get("chatUid");
if (!uid) { uid = Array.from(crypto.getRandomValues(new Uint8Array(16)), b => b.toString(16).padStart(2, "0")).join(""); ls.set("chatUid", uid); }
(function readHash() {                       // 登录链接 #k=…&n=… ；通知点开 #c=…
  const h = location.hash.slice(1); if (!h) return;
  const p = new URLSearchParams(h);
  if (p.get("k")) { uid = p.get("k"); ls.set("chatUid", uid); if (p.get("n")) ls.set("chatName", p.get("n")); }
  if (p.get("c")) pendingOpen = p.get("c");
  history.replaceState(null, "", location.pathname);
})();
const isIOS = /iP(hone|ad|od)/.test(navigator.userAgent) || (navigator.platform === "MacIntel" && navigator.maxTouchPoints > 1);
const standalone = matchMedia("(display-mode: standalone)").matches || navigator.standalone === true;
const COLORS = ["#5b8ff9","#f6903d","#61ddaa","#e8684a","#9270ca","#269a99","#ff99c3","#d4a017"];
function colorOf(name) { let h = 0; for (const c of name) h = (h * 31 + c.codePointAt(0)) >>> 0; return COLORS[h % COLORS.length]; }
const icon = id => `<svg class="i"><use href="#${id}"/></svg>`;

let toastTimer;
function toast(t, ms = 2200) { const el = $("toast"); el.textContent = t; el.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => el.hidden = true, ms); }

/* ================= 提示音 ================= */
let actx = null;
function unlockAudio() {
  try {
    if (!actx) actx = new (window.AudioContext || window.webkitAudioContext)();
    if (actx.state !== "running") {
      actx.resume();
      const b = actx.createBuffer(1, 1, 22050), s = actx.createBufferSource(); s.buffer = b; s.connect(actx.destination); s.start(0);
    }
  } catch (e) {}
}
document.addEventListener("pointerdown", unlockAudio, { passive:true });
document.addEventListener("keydown", unlockAudio);
function tone(freq, start, dur, vol = 0.22) {
  const o = actx.createOscillator(), g = actx.createGain();
  o.type = "sine"; o.frequency.value = freq;
  g.gain.setValueAtTime(0.0001, start); g.gain.exponentialRampToValueAtTime(vol, start + 0.015);
  g.gain.exponentialRampToValueAtTime(0.0001, start + dur);
  o.connect(g); g.connect(actx.destination); o.start(start); o.stop(start + dur + 0.05);
}
function ding() {
  if (navigator.vibrate && document.hidden) navigator.vibrate(150);
  if (!soundOn || !actx || actx.state !== "running") return;
  const t = actx.currentTime; tone(988, t, 0.22); tone(1319, t + 0.11, 0.38);
}
let ringTimer = null;
function startRing() {
  stopRing();
  const once = () => {
    if (navigator.vibrate) navigator.vibrate([400, 200, 400]);
    if (!soundOn || !actx || actx.state !== "running") return;
    const t = actx.currentTime;
    [0, 0.45].forEach(d => { tone(659, t + d, 0.28, 0.3); tone(784, t + d + 0.14, 0.3, 0.3); });
  };
  once(); ringTimer = setInterval(once, 2600);
}
function stopRing() { clearInterval(ringTimer); ringTimer = null; if (navigator.vibrate) navigator.vibrate(0); }
function paintSound() { $("soundBtn").innerHTML = icon(soundOn ? "i-bell" : "i-bell-off"); $("soundBtn").title = soundOn ? "提示音：开" : "提示音：关"; }
$("soundBtn").onclick = () => {
  soundOn = !soundOn; ls.set("chatSound", soundOn ? "1" : "0");
  paintSound(); toast(soundOn ? "提示音已打开" : "提示音已关闭"); unlockAudio(); if (soundOn) setTimeout(ding, 50);
};
paintSound();

/* ================= 系统通知 / 推送 ================= */
if ("serviceWorker" in navigator) {
  navigator.serviceWorker.register("/sw.js").then(r => { swReg = r; }).catch(() => {});
  navigator.serviceWorker.addEventListener("message", e => { if (e.data && e.data.open) openWhenReady(e.data.open); });
}
function b64u(buf) { return btoa(String.fromCharCode(...new Uint8Array(buf))).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, ""); }
function u8(b64) { const s = atob(b64.replace(/-/g, "+").replace(/_/g, "/") + "=".repeat((4 - b64.length % 4) % 4)); return Uint8Array.from(s, c => c.charCodeAt(0)); }
const withTimeout = (p, ms) => Promise.race([p, new Promise((_, rej) => setTimeout(() => rej(new Error("timeout")), ms))]);

async function setupPush() {
  if (!vapidKey || !("PushManager" in window) || !("serviceWorker" in navigator)) return false;
  try {
    const reg = await withTimeout(navigator.serviceWorker.ready, 8000);
    let sub = await reg.pushManager.getSubscription();
    const k = sub && sub.options && sub.options.applicationServerKey;
    if (sub && k && b64u(k) !== vapidKey) { await sub.unsubscribe(); sub = null; }
    if (!sub) sub = await reg.pushManager.subscribe({ userVisibleOnly:true, applicationServerKey:u8(vapidKey) });
    pushActive = true;
    if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"push_sub", sub:sub.toJSON() }));
    return true;
  } catch (e) { console.warn("push", e); return false; }
}
function notify(title, body, tag, conv, call) {
  if (pushActive || !document.hidden) return;               // 有推送时由后台推送负责弹通知
  if (!("Notification" in window) || Notification.permission !== "granted") return;
  const opts = { body, tag, icon:"/icon-192.png", badge:"/icon-192.png", renotify:true, requireInteraction:!!call, data:{ conv } };
  if (swReg) swReg.showNotification(title, opts).catch(() => {});
  else try { const n = new Notification(title, opts); n.onclick = () => { window.focus(); openWhenReady(conv); }; } catch (e) {}
}
function updateAlertBar() {
  let msg = "", key = "", canAsk = false;
  if (isIOS && !standalone && !("PushManager" in window)) {
    key = "ios"; msg = "想在 iPhone 锁屏收到消息提醒：点 Safari 底部的「分享」→「添加到主屏幕」，以后从桌面图标打开。";
  } else if ("Notification" in window) {
    if (Notification.permission === "default") { key = "ask"; msg = "开启消息提醒，切到别的 App 或锁屏也能收到。"; canAsk = true; }
    else if (Notification.permission === "denied") { key = "denied"; msg = "消息提醒被关掉了，可以在浏览器的网站设置里重新允许通知。"; }
  }
  const bar = $("alertBar");
  if (!msg || !joined || ls.get("alertX") === key) { bar.hidden = true; return; }
  bar.querySelector(".t").textContent = msg; $("alertOn").hidden = !canAsk; bar.dataset.key = key; bar.hidden = false;
}
$("alertOn").onclick = async () => {
  unlockAudio();
  let p = "denied";
  try { p = await Notification.requestPermission(); } catch (e) {}
  if (p === "granted") {
    const ok = await setupPush();
    toast(ok ? "已开启，锁屏也能收到提醒" : "已开启（页面开着时提醒）");
  }
  updateAlertBar();
};
$("alertX").onclick = () => { ls.set("alertX", $("alertBar").dataset.key); $("alertBar").hidden = true; };

function sendVis() { if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"vis", visible:!document.hidden })); }
document.addEventListener("visibilitychange", () => {
  if (!document.hidden && current) { getConv(current).unread = 0; renderHomeSoon(); }
  updateDocTitle(); sendVis();
});

/* ================= 头像 ================= */
function makeAvatar(name, src) {
  if (src) { const img = document.createElement("img"); img.className = "avatar"; img.alt = ""; img.src = src; img.dataset.name = name; return img; }
  const d = document.createElement("div"); d.className = "avatar"; d.dataset.name = name;
  d.style.background = colorOf(name); d.textContent = [...name][0] || "?"; return d;
}
function wireAvatar(av, name) {
  if (name === myName) av.onclick = openSheet;
  else av.onclick = () => openConv("dm:" + name);
}
function refreshAvatars() {
  document.querySelectorAll("#list .avatar").forEach(el => {
    const n = el.dataset.name, fresh = makeAvatar(n, avatars[n]);
    wireAvatar(fresh, n); el.replaceWith(fresh);
  });
  renderHomeSoon();
}
function showPreview() {
  const p = $("preview"), name = $("nick").value.trim() || myName || "我";
  p.replaceChildren(); p.style.background = "";
  if (draftAvatar) { const img = document.createElement("img"); img.src = draftAvatar; img.style.cssText = "width:100%;height:100%;object-fit:cover;border-radius:8px"; p.append(img); }
  else { p.style.background = colorOf(name); p.textContent = [...name][0] || "?"; }
  $("clear").hidden = !draftAvatar;
}
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
  $("sheetTitle").textContent = "我的资料"; $("join").textContent = "保存"; $("cancel").hidden = false; $("loginLink").hidden = false;
  showPreview(); $("sheet").hidden = false;
}
$("loginLink").onclick = async () => {
  const link = `${location.origin}/#k=${encodeURIComponent(uid)}&n=${encodeURIComponent(myName)}`;
  let ok = false;
  try { await navigator.clipboard.writeText(link); ok = true; } catch (e) {}
  if (ok) toast("链接已复制。在另一台设备的浏览器里打开它，就能用同一个账号，私聊记录也在。这个链接别发给别人。", 5000);
  else window.prompt("复制这个链接，在另一台设备上打开（别发给别人）：", link);
};

/* ================= 会话（群聊 + 私聊） ================= */
const convs = new Map();
let current = null;                                  // 正在看的会话；null = 聊天列表
const peerOf = key => key.slice(3);
function convKey(m) { return m.to ? "dm:" + (m.name === myName ? m.to : m.name) : "group"; }
function getConv(key) {
  let c = convs.get(key);
  if (!c) { c = { key, msgs:[], unread:0, lastTs:0, rTs:0 }; convs.set(key, c); }
  return c;
}
function convTitle(key) { return key === "group" ? "群聊" : peerOf(key); }
function totalUnread() { let n = 0; convs.forEach(c => n += c.unread); return n; }
function updateDocTitle() {
  const n = totalUnread();
  document.title = n ? `(${n}) 群聊` : "群聊";
  const others = n - (current ? getConv(current).unread : 0);
  $("back").querySelector(".ub").textContent = others > 0 ? String(others) : "";
}
function previewOf(m, key) {
  if (m.type === "system") return m.text;
  const body = m.type === "image" ? "[图片]" : m.type === "video" ? "[视频]" : m.text;
  return key === "group" ? `${m.name === myName ? "我" : m.name}: ${body}` : body;
}
function fmtShort(ts) {
  const d = new Date(ts), now = new Date();
  const day = x => new Date(x.getFullYear(), x.getMonth(), x.getDate()).getTime();
  const diff = Math.round((day(now) - day(d)) / 86400000);
  if (diff === 0) return d.toLocaleTimeString("zh-CN", { hour:"2-digit", minute:"2-digit", hour12:false });
  if (diff === 1) return "昨天";
  return `${d.getMonth()+1}/${d.getDate()}`;
}
let homeQueued = false;
function renderHomeSoon() { if (homeQueued) return; homeQueued = true; requestAnimationFrame(() => { homeQueued = false; renderHome(); }); }
function renderHome() {
  const keys = new Set(["group"]);
  members.forEach(n => { if (n !== myName) keys.add("dm:" + n); });
  convs.forEach((c, k) => { if (k !== "group" && c.msgs.length) keys.add(k); });
  const arr = [...keys].map(getConv).sort((a, b) => {
    if (a.key === "group") return -1; if (b.key === "group") return 1;
    return (b.lastTs - a.lastTs) || peerOf(a.key).localeCompare(peerOf(b.key), "zh");
  });
  const box = $("convList"); box.replaceChildren();
  for (const c of arr) {
    const row = document.createElement("div"); row.className = "conv"; row.dataset.key = c.key;
    const av = document.createElement("div"); av.className = "av";
    if (c.key === "group") { const g = document.createElement("div"); g.className = "avatar gav"; g.innerHTML = icon("i-group"); av.append(g); }
    else {
      const p = peerOf(c.key); av.append(makeAvatar(p, avatars[p]));
      if (users.includes(p)) { const d = document.createElement("span"); d.className = "dot"; d.title = "在线"; av.append(d); }
    }
    if (c.unread) { const b = document.createElement("span"); b.className = "badge"; b.textContent = c.unread > 99 ? "99+" : c.unread; av.append(b); }
    const main = document.createElement("div"); main.className = "cmain";
    const top = document.createElement("div"); top.className = "ctop";
    const t = document.createElement("span"); t.className = "ctitle"; t.textContent = c.key === "group" ? `群聊（${users.length}人在线）` : peerOf(c.key);
    const tm = document.createElement("span"); tm.className = "ctime";
    const last = [...c.msgs].reverse().find(m => !m.quiet);
    if (last) tm.textContent = fmtShort(last.ts);
    top.append(t, tm);
    const pv = document.createElement("div"); pv.className = "cprev";
    const cl = calls.get(c.key);
    if (cl && !(inCall && callKey === c.key)) { const s = document.createElement("span"); s.className = "live"; s.textContent = `[${cl.media === "video" ? "视频" : "语音"}通话中] `; pv.append(s); }
    pv.append(last ? previewOf(last, c.key) : (c.key === "group" ? "" : users.includes(peerOf(c.key)) ? "在线 · 点这里私聊" : "点这里私聊"));
    main.append(top, pv); row.append(av, main);
    row.onclick = () => openConv(c.key);
    box.append(row);
  }
  updateDocTitle();
}
function setChatHeader() {
  if (!current) return;
  $("chatTitle").textContent = convTitle(current);
  $("chatCount").textContent = current === "group" ? `（${users.length}）` : (users.includes(peerOf(current)) ? "" : "（离线）");
}
function openConv(key, push = true) {
  if (!joined || !myName) { pendingOpen = key; return; }
  if (key !== "group" && !key.startsWith("dm:")) return;
  if (key === "dm:" + myName) return;
  const same = current === key;
  current = key; getConv(key).unread = 0;
  $("home").hidden = true; $("chat").hidden = false;
  list.classList.toggle("dm", key !== "group");
  setChatHeader(); setMore(false); renderConv(key); updateCallBar(); renderHomeSoon();
  if (push && !same) history.pushState({ c:key }, "");
}
function openWhenReady(key) { if (joined && myName) openConv(key); else pendingOpen = key; }
function goHome() {
  current = null; setMore(false); textEl.blur();
  $("chat").hidden = true; $("home").hidden = false; renderHome();
}
$("back").onclick = () => { if (history.state && history.state.c) history.back(); else goHome(); };
window.addEventListener("popstate", () => { if (current) goHome(); });

/* ================= 消息列表 ================= */
function fmtTime(ts) {
  const d = new Date(ts), now = new Date();
  const hm = d.toLocaleTimeString("zh-CN", { hour:"2-digit", minute:"2-digit", hour12:false });
  const day = x => new Date(x.getFullYear(), x.getMonth(), x.getDate()).getTime();
  const diff = Math.round((day(now) - day(d)) / 86400000);
  if (diff === 0) return hm;
  if (diff === 1) return "昨天 " + hm;
  return `${d.getMonth()+1}月${d.getDate()}日 ${hm}`;
}
function fitSize(w, h, kind) {
  if (!w || !h) return kind === "video" ? { w:220, h:160 } : { w:160, h:160 };
  const maxW = Math.min(220, (list.clientWidth || 360) * 0.58), maxH = 260, s = Math.min(maxW / w, maxH / h, 1);
  return { w:Math.max(Math.round(w * s), 70), h:Math.max(Math.round(h * s), 70) };
}
function mediaBox(kind, url, w, h) {
  const box = document.createElement("div"); box.className = "media";
  const sz = fitSize(w, h, kind); box.style.width = sz.w + "px"; box.style.height = sz.h + "px";
  if (kind === "image") {
    const img = new Image(); img.alt = ""; img.src = url; img.onclick = () => viewImage(url); box.append(img);
  } else {
    const v = document.createElement("video"); v.controls = true; v.playsInline = true; v.preload = "metadata";
    v.src = url.startsWith("blob:") ? url : url + "#t=0.1"; box.append(v);
  }
  return box;
}
function buildRow(m) {
  const mine = m.name === myName;
  const row = document.createElement("div"); row.className = "msg" + (mine ? " me" : "");
  const av = makeAvatar(m.name, avatars[m.name]); wireAvatar(av, m.name);
  const body = document.createElement("div"); body.className = "body";
  const name = document.createElement("div"); name.className = "name"; name.textContent = m.name;
  let content;
  if (m.type === "chat") { content = document.createElement("div"); content.className = "bubble"; content.textContent = m.text; }
  else if (m.expired) { content = document.createElement("div"); content.className = "bubble gone"; content.textContent = m.type === "image" ? "[图片已过期]" : "[视频已过期]"; }
  else content = mediaBox(m.type, m.url, m.w, m.h);
  body.append(name, content); row.append(av, body);
  return row;
}
function appendToList(m, c) {
  const ts = m.ts || Date.now();
  if (ts - c.rTs > 5 * 60 * 1000) { const t = document.createElement("div"); t.className = "time"; t.textContent = fmtTime(ts); list.append(t); }
  c.rTs = ts;
  if (m.type === "system") { const s = document.createElement("div"); s.className = "sys"; s.textContent = m.text; list.append(s); }
  else list.append(buildRow(m));
}
function renderConv(key) {
  const c = getConv(key); c.rTs = 0; list.replaceChildren();
  c.msgs.forEach(m => appendToList(m, c));
  pending.forEach(p => { if (p.key === key) list.append(p.row); });
  list.scrollTop = list.scrollHeight;
}
const pending = new Map();   // 正在上传的消息
const MSG_TYPES = ["system", "chat", "image", "video"];
function add(m, live) {
  if (!MSG_TYPES.includes(m.type)) return;
  const key = convKey(m), c = getConv(key);
  c.msgs.push(m); if (c.msgs.length > 400) c.msgs.shift();
  if (!m.quiet) c.lastTs = Math.max(c.lastTs, m.ts || 0);
  if (m.cid && pending.has(m.cid) && m.name === myName) {      // 自己上传完成：把占位换成正式消息
    const p = pending.get(m.cid); pending.delete(m.cid);
    if (p.row.isConnected) p.row.replaceWith(buildRow(m));
    if (p.local) setTimeout(() => URL.revokeObjectURL(p.local), 5000);
    renderHomeSoon(); return;
  }
  if (key === current) {
    const atBottom = list.scrollHeight - list.scrollTop - list.clientHeight < 80;
    appendToList(m, c);
    if (atBottom || m.name === myName) list.scrollTop = list.scrollHeight;
  }
  if (live && m.type !== "system" && m.name !== myName) {
    if (key !== current || document.hidden) c.unread++;
    if (!document.hidden || !pushActive) ding();
    const body = m.type === "image" ? "[图片]" : m.type === "video" ? "[视频]" : m.text;
    if (key === "group") notify("群聊", `${m.name}: ${body}`, "m-" + (m.id || m.ts), key);
    else notify(m.name, body, "m-" + (m.id || m.ts), key);
  }
  if (live) renderHomeSoon();
}
function viewImage(url) { const v = $("viewer"); v.querySelector("img").src = url; v.hidden = false; }
$("viewer").onclick = () => { $("viewer").hidden = true; $("viewer").querySelector("img").src = ""; };

/* ================= 连接 ================= */
function setStatus(t) { document.querySelectorAll(".status").forEach(el => el.textContent = t); }
function connect(name) {
  const proto = location.protocol === "https:" ? "wss" : "ws";
  ws = new WebSocket(`${proto}://${location.host}/ws`);
  ws.onopen = () => { ws.send(JSON.stringify({ type:"join", name, uid, avatar:myAvatar, visible:!document.hidden })); setStatus(""); };
  ws.onmessage = e => {
    const m = JSON.parse(e.data);
    if (m.type === "welcome") {
      myName = m.name; avatars = m.avatars || {}; token = m.token; vapidKey = m.vapid; iceServers = m.ice || []; limits = m.limits || limits;
      if (myName !== name) ls.set("chatName", myName);
      const unread = new Map([...convs].map(([k, c]) => [k, c.unread]));
      convs.clear();
      m.history.forEach(x => add(x, false));
      unread.forEach((n, k) => { if (n) getConv(k).unread = n; });
      calls.clear(); (m.calls || []).forEach(c => onCallState(c));
      if ("Notification" in window && Notification.permission === "granted") setupPush();
      updateAlertBar();
      if (pendingOpen) { const k = pendingOpen; pendingOpen = null; openConv(k); }
      else if (current) { setChatHeader(); renderConv(current); }
      renderHome();
    }
    else if (m.type === "avatars") { avatars = m.avatars; refreshAvatars(); }
    else if (m.type === "users") { users = m.users; members = m.members || users; setChatHeader(); renderHomeSoon(); }
    else if (m.type === "call_state") onCallState(m.call);
    else if (m.type === "call_joined") onCallJoined(m);
    else if (m.type === "call_declined") onDeclined(m.name);
    else if (m.type === "signal") onSignal(m.from, m.data);
    else if (m.type === "toast") toast(m.text);
    else add(m, true);
  };
  ws.onclose = () => {
    setStatus("连接中…");
    if (inCall) endLocal("网络断开，通话已结束");
    setTimeout(() => connect(myName || name), 3000);
  };
}

function join() {
  unlockAudio();
  if (joined) {                        // 已经进来了：只是换头像
    myAvatar = draftAvatar; ls.set("chatAvatar", myAvatar);
    if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"avatar", avatar:myAvatar }));
    $("sheet").hidden = true; return;
  }
  const name = $("nick").value.trim();
  if (!name) return $("nick").focus();
  myAvatar = draftAvatar; ls.set("chatName", name); ls.set("chatAvatar", myAvatar);
  joined = true; $("profileBtn").hidden = false; $("soundBtn").hidden = false;
  $("sheet").hidden = true; connect(name);
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

/* ================= 输入框 / 更多面板 ================= */
function grow() {
  textEl.style.height = "38px"; textEl.style.height = Math.min(textEl.scrollHeight, 120) + "px";
  const has = !!textEl.value.trim(); sendBtn.hidden = !has; $("plus").hidden = has;
}
const toOf = key => key && key !== "group" ? peerOf(key) : undefined;
function send() {
  const text = textEl.value.trim();
  if (!text || !ws || ws.readyState !== 1 || !current) return;
  ws.send(JSON.stringify({ text, to:toOf(current) })); textEl.value = ""; grow(); textEl.focus();
}
function setMore(open) { $("more").hidden = !open; $("foot").classList.toggle("open", open); if (open) list.scrollTop = list.scrollHeight; }
$("plus").onclick = () => { setMore($("more").hidden); if (!$("more").hidden) textEl.blur(); };
textEl.onfocus = () => setMore(false);
list.addEventListener("pointerdown", () => setMore(false));
$("more").onclick = e => {
  const b = e.target.closest("button"); if (!b) return;
  const a = b.dataset.act;
  if (a === "album") $("pickAlbum").click();
  else if (a === "photo") $("pickPhoto").click();
  else if (a === "record") $("pickVideo").click();
  else if (a === "vcall") { setMore(false); startOrJoin("video", current); }
  else if (a === "acall") { setMore(false); startOrJoin("audio", current); }
};
["pickAlbum", "pickPhoto", "pickVideo"].forEach(id => $(id).onchange = e => {
  const files = [...e.target.files]; e.target.value = ""; setMore(false); sendFiles(files, current);
});
$("join").onclick = join;
$("nick").onkeydown = e => { if (e.key === "Enter" && !e.isComposing) join(); };
textEl.oninput = grow;
textEl.onkeydown = e => { if (e.key === "Enter" && !e.shiftKey && !e.isComposing) { e.preventDefault(); send(); } };
sendBtn.onclick = send;

/* ================= 发图片 / 视频 ================= */
const VIDEO_EXT = { mp4:"video/mp4", m4v:"video/x-m4v", mov:"video/quicktime", webm:"video/webm", "3gp":"video/3gpp" };
function videoType(f) {
  if (["video/mp4","video/quicktime","video/webm","video/3gpp","video/x-m4v"].includes(f.type)) return f.type;
  return VIDEO_EXT[(f.name.split(".").pop() || "").toLowerCase()] || null;
}
const isVideo = f => f.type.startsWith("video/") || !!VIDEO_EXT[(f.name.split(".").pop() || "").toLowerCase()];
function loadImg(file) {
  return new Promise((res, rej) => {
    const u = URL.createObjectURL(file), i = new Image();
    i.onload = () => { URL.revokeObjectURL(u); res(i); };
    i.onerror = () => { URL.revokeObjectURL(u); rej(new Error("bad image")); };
    i.src = u;
  });
}
async function prepImage(file) {
  const i = await loadImg(file);
  if (file.type === "image/gif" && file.size < 8e6) return { blob:file, type:"image/gif", w:i.naturalWidth, h:i.naturalHeight };
  const max = 1920, s = Math.min(1, max / Math.max(i.naturalWidth, i.naturalHeight));
  const w = Math.round(i.naturalWidth * s), h = Math.round(i.naturalHeight * s);
  const c = document.createElement("canvas"); c.width = w; c.height = h;
  const ctx = c.getContext("2d"); ctx.fillStyle = "#fff"; ctx.fillRect(0, 0, w, h); ctx.drawImage(i, 0, 0, w, h);
  const blob = await new Promise(r => c.toBlob(r, "image/jpeg", 0.85));
  if (!blob) throw new Error("encode");
  return { blob, type:"image/jpeg", w, h };
}
function videoMeta(file) {
  return new Promise(res => {
    const v = document.createElement("video"), u = URL.createObjectURL(file); let done = false;
    const fin = r => { if (done) return; done = true; URL.revokeObjectURL(u); res(r); };
    v.preload = "metadata"; v.muted = true;
    v.onloadedmetadata = () => fin({ w:v.videoWidth, h:v.videoHeight, dur:isFinite(v.duration) ? v.duration : 0 });
    v.onerror = () => fin({ w:0, h:0, dur:0 }); setTimeout(() => fin({ w:0, h:0, dur:0 }), 5000);
    v.src = u;
  });
}
function addPending(kind, localUrl, w, h, key) {
  const cid = Math.random().toString(36).slice(2, 12);
  const row = document.createElement("div"); row.className = "msg me";
  const av = makeAvatar(myName, avatars[myName]); av.onclick = openSheet;
  const body = document.createElement("div"); body.className = "body";
  const box = mediaBox(kind, localUrl, w, h);
  const v = box.querySelector("video"); if (v) v.controls = false;
  const up = document.createElement("div"); up.className = "up"; up.textContent = "0%"; box.append(up);
  body.append(box); row.append(av, body);
  if (key === current) { list.append(row); list.scrollTop = list.scrollHeight; }
  const p = { row, local:localUrl, up, key }; pending.set(cid, p);
  return { cid, p };
}
function upload(kind, blob, type, meta, cid, key, onProgress) {
  return new Promise((res, rej) => {
    const q = new URLSearchParams({ token, kind, cid, w:meta.w || 0, h:meta.h || 0, dur:Math.round(meta.dur || 0) });
    if (toOf(key)) q.set("to", toOf(key));
    const x = new XMLHttpRequest(); x.open("POST", "/upload?" + q);
    x.setRequestHeader("Content-Type", type);
    x.upload.onprogress = e => { if (e.lengthComputable) onProgress(e.loaded / e.total); };
    x.onload = () => { if (x.status === 200) res(); else { let msg = ""; try { msg = JSON.parse(x.responseText).error; } catch (e) {} rej(new Error(msg || "上传失败")); } };
    x.onerror = () => rej(new Error("网络不好，上传失败"));
    x.send(blob);
  });
}
async function sendFiles(files, key) {
  if (!ws || ws.readyState !== 1 || !token) return toast("还没连上，稍后再试");
  if (!key) return;
  for (const f of files) {
    let kind, blob, type, meta;
    try {
      if (isVideo(f)) {
        kind = "video"; type = videoType(f); blob = f;
        if (!type) { toast("这种视频格式发不了"); continue; }
        if (f.size > limits.video_mb * 1048576) { toast(`视频太大了（最大 ${limits.video_mb}MB），剪短一点再发`); continue; }
        meta = await videoMeta(f);
      } else if (f.type.startsWith("image/") || /\.(jpe?g|png|gif|webp|heic|heif)$/i.test(f.name)) {
        kind = "image"; const r = await prepImage(f); blob = r.blob; type = r.type; meta = { w:r.w, h:r.h };
        if (blob.size > limits.image_mb * 1048576) { toast("图片太大了"); continue; }
      } else { toast("只能发图片和视频"); continue; }
    } catch (e) { toast("这个文件打不开，换一个试试"); continue; }
    const local = URL.createObjectURL(blob);
    const { cid, p } = addPending(kind, local, meta.w, meta.h, key);
    try {
      await upload(kind, blob, type, meta, cid, key, r => { p.up.textContent = Math.round(r * 100) + "%"; if (r >= 1) p.up.textContent = "处理中…"; });
      if (pending.has(cid)) p.up.hidden = true;
    } catch (e) {
      p.up.textContent = (e.message || "发送失败") + "（点一下移除）"; p.up.classList.add("err");
      p.up.onclick = () => { p.row.remove(); pending.delete(cid); URL.revokeObjectURL(local); };
    }
  }
}

/* ================= 语音 / 视频通话 ================= */
const calls = new Map();                 // 会话 key -> 进行中的通话
let callKey = null, inCall = false, callMedia = "video", localStream = null;
let ringKey = null, ringStart = 0, declinedFor = null, declined = new Set();
const rung = new Map();
let connectedAt = 0, aloneTimer = null, clockTimer = null, ringStopTimer = null, wakeLock = null;
let micOn = true, camOn = true, facing = "user";
const peers = new Map(), tiles = new Map();
let sigChain = Promise.resolve();
const sig = (to, data) => { if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"signal", to, data })); };
const label = media => media === "video" ? "视频" : "语音";
const myCall = () => callKey ? calls.get(callKey) : null;
function callKeyOf(c) { return c.invite ? "dm:" + (c.invite.find(n => n !== myName) || myName) : "group"; }

function onCallState(c) {
  const key = callKeyOf(c);
  if (c.ended) calls.delete(key); else calls.set(key, c);
  if (inCall && key === callKey) {
    if (c.ended || !c.members.includes(myName)) endLocal("通话已结束");
    else {
      rung.set(key, c.start);
      if (c.members.length === 1 && connectedAt) { hangup(); toast("对方已挂断"); }
      else {
        for (const n of [...peers.keys()]) if (!c.members.includes(n)) { closePeer(n); toast(`${n} 已挂断`); }
        for (const n of [...tiles.keys()]) if (n !== myName && !c.members.includes(n)) removeTile(n);
        updateCallTop();
      }
    }
  } else if (c.ended) {
    if (ringKey === key) hideRing();
  } else if (!inCall) {
    const fresh = Date.now() - c.start < 60000;
    if (rung.get(key) !== c.start && declinedFor !== c.start && fresh && !c.members.includes(myName) && c.members.length) {
      rung.set(key, c.start); showRing(c, key);
    }
  }
  updateCallBar(); renderHomeSoon();
}
function updateCallBar() {
  const bar = $("callBar"), c = current && calls.get(current);
  if (!c || (inCall && callKey === current) || c.members.includes(myName)) { bar.hidden = true; return; }
  bar.textContent = current === "group"
    ? `${c.by} 发起的群${label(c.media)}通话进行中（${c.members.length}人）· 点这里加入`
    : `${c.by} 的${label(c.media)}通话进行中 · 点这里加入`;
  bar.hidden = false;
}
function showRing(c, key) {
  const av = makeAvatar(c.by, avatars[c.by]); av.classList.add("big");
  $("ringAv").replaceChildren(av);
  $("ringName").textContent = c.by;
  $("ringText").textContent = key === "group" ? `邀请你加入群${label(c.media)}通话…` : `邀请你${label(c.media)}通话…`;
  ringKey = key; ringStart = c.start;
  $("ring").hidden = false; startRing();
  notify(c.by, $("ringText").textContent, "call-" + c.start, key, true);
  clearTimeout(ringStopTimer); ringStopTimer = setTimeout(hideRing, 60000);
}
function hideRing() { $("ring").hidden = true; stopRing(); clearTimeout(ringStopTimer); ringKey = null; }
$("accept").onclick = () => { const k = ringKey, c = calls.get(k); hideRing(); if (k) { openConv(k); startOrJoin(c ? c.media : "video", k); } };
$("decline").onclick = () => {
  if (ringKey) { declinedFor = ringStart; if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"call_decline", to:toOf(ringKey) })); }
  hideRing();
};
$("callBar").onclick = () => { const c = current && calls.get(current); if (c) startOrJoin(c.media, current); };

async function getMedia(media) {
  return navigator.mediaDevices.getUserMedia({
    audio:{ echoCancellation:true, noiseSuppression:true, autoGainControl:true },
    video:media === "video" ? { facingMode:facing, width:{ ideal:960 }, height:{ ideal:720 } } : false
  });
}
async function startOrJoin(media, key) {
  if (inCall || !key) return;
  unlockAudio();
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia || !window.RTCPeerConnection) return toast("这个浏览器不支持通话，换 Chrome 或 Safari 试试");
  if (!ws || ws.readyState !== 1) return toast("还没连上，稍后再试");
  const existing = calls.get(key);
  if (existing) media = existing.media;
  if (!existing && key === "group" && users.length < 2) return toast("群里现在只有你一个人在线");
  facing = "user";
  try { localStream = await getMedia(media); }
  catch (e) { return toast(media === "video" ? "没有拿到摄像头和麦克风权限，请在浏览器设置里允许" : "没有拿到麦克风权限，请在浏览器设置里允许", 3500); }
  inCall = true; callKey = key; callMedia = media; micOn = true; camOn = media === "video"; connectedAt = 0; declined = new Set();
  $("callBar").hidden = true; showCallView();
  ws.send(JSON.stringify({ type:existing ? "call_join" : "call_start", media, to:toOf(key) }));
  if (!existing && key !== "group" && !users.includes(peerOf(key))) toast(`${peerOf(key)} 现在不在线，已给 TA 发提醒`, 3000);
  try { wakeLock = await navigator.wakeLock.request("screen"); } catch (e) {}
}
function showCallView() {
  $("callView").hidden = false;
  const lv = $("localVid");
  lv.srcObject = localStream; lv.hidden = callMedia !== "video"; lv.classList.toggle("mirror", facing === "user");
  lv.play().catch(() => {});
  $("btnCam").hidden = callMedia !== "video"; $("btnFlip").hidden = true;
  if (callMedia === "video" && navigator.mediaDevices.enumerateDevices)
    navigator.mediaDevices.enumerateDevices().then(d => { $("btnFlip").hidden = d.filter(x => x.kind === "videoinput").length < 2; }).catch(() => {});
  paintCallBtns(); updateCallTop();
}
function updateCallTop() {
  if (!inCall) return;
  const c = myCall();
  const others = (c ? c.members : []).filter(n => n !== myName);
  $("callTitle").textContent = others.length ? others.join("、") : (callKey === "group" ? `群${label(callMedia)}通话` : peerOf(callKey));
  if (!connectedAt) $("callTime").textContent = others.length ? "连接中…" : "等待对方接听…";
  if (!others.length && !aloneTimer) aloneTimer = setTimeout(() => { const cc = myCall(); if (inCall && !connectedAt && (!cc || cc.members.length < 2)) { toast("对方无应答"); hangup(); } }, 60000);
  if (!tiles.size && callMedia === "audio") tileFor(myName).st.textContent = "";
  updateSolo();
}
function updateSolo() { $("callView").classList.toggle("solo", ![...tiles.keys()].some(n => n !== myName)); }
function onCallJoined(m) {
  if (!inCall) return;
  callMedia = m.media;
  m.peers.forEach(n => sigChain = sigChain.then(() => offerTo(n)).catch(e => console.warn(e)));
}
function onDeclined(name) {
  if (!inCall) return;
  toast(`${name} 拒绝了通话`); declined.add(name);
  const c = myCall();
  const others = callKey === "group" ? users.filter(u => u !== myName) : [peerOf(callKey)];
  if (c && c.members.length === 1 && others.every(u => declined.has(u))) setTimeout(hangup, 1200);
}
function tileFor(name) {
  let t = tiles.get(name); if (t) return t;
  if (name !== myName && tiles.has(myName)) removeTile(myName);
  const el = document.createElement("div"); el.className = "tile";
  const av = makeAvatar(name, avatars[name]); av.classList.add("big");
  const st = document.createElement("div"); st.className = "tstate"; st.textContent = "连接中…";
  const lb = document.createElement("div"); lb.className = "tlabel"; lb.textContent = name;
  const media = document.createElement(callMedia === "video" ? "video" : "audio");
  media.autoplay = true; media.playsInline = true; media.setAttribute("playsinline", "");
  el.append(av, st, media, lb); $("tiles").append(el);
  t = { el, media, st }; tiles.set(name, t); layoutTiles(); return t;
}
function removeTile(name) { const t = tiles.get(name); if (t) { t.media.srcObject = null; t.el.remove(); tiles.delete(name); layoutTiles(); } }
function layoutTiles() { $("tiles").className = "n" + Math.max(1, tiles.size); updateSolo(); }
function makePeer(name) {
  const pc = new RTCPeerConnection({ iceServers });
  const p = { pc, queue:[], restarted:false }; peers.set(name, p);
  localStream.getTracks().forEach(t => pc.addTrack(t, localStream));
  pc.onicecandidate = e => { if (e.candidate) sig(name, { candidate:e.candidate.toJSON ? e.candidate.toJSON() : e.candidate }); };
  pc.ontrack = e => {
    const t = tileFor(name), s = e.streams[0] || new MediaStream([e.track]);
    if (t.media.srcObject !== s) t.media.srcObject = s;
    t.media.play().catch(() => {});
    if (e.track.kind === "video") t.el.classList.add("has-video");
  };
  pc.oniceconnectionstatechange = () => {
    const s = pc.iceConnectionState, t = tileFor(name);
    if (s === "connected" || s === "completed") {
      t.st.textContent = "";
      if (!connectedAt) { connectedAt = Date.now(); clearTimeout(aloneTimer); startClock(); }
    } else if (s === "failed") {
      t.st.textContent = "连接失败（网络不通）";
      if (p.offerer && !p.restarted) { p.restarted = true; sigChain = sigChain.then(() => offerTo(name, true)).catch(() => {}); }
    } else if (s === "disconnected") t.st.textContent = "网络不稳定…";
    else if (s === "checking") t.st.textContent = "连接中…";
  };
  return p;
}
async function offerTo(name, restart) {
  if (!inCall) return;
  let p = peers.get(name);
  if (!p) p = makePeer(name);
  p.offerer = true;
  tileFor(name);
  const o = await p.pc.createOffer(restart ? { iceRestart:true } : undefined);
  await p.pc.setLocalDescription(o);
  sig(name, { sdp:{ type:p.pc.localDescription.type, sdp:p.pc.localDescription.sdp } });
  if (callMedia === "video") sig(name, { cam:camOn });
}
function onSignal(from, d) { sigChain = sigChain.then(() => handleSignal(from, d)).catch(e => console.warn("signal", e)); }
async function handleSignal(from, d) {
  if (!inCall) return;
  let p = peers.get(from);
  if (d.sdp) {
    if (d.sdp.type === "offer" && !p) { p = makePeer(from); tileFor(from); }
    if (!p) return;
    await p.pc.setRemoteDescription(d.sdp);
    for (const c of p.queue) await p.pc.addIceCandidate(c).catch(() => {});
    p.queue = [];
    if (d.sdp.type === "offer") {
      await p.pc.setLocalDescription(await p.pc.createAnswer());
      sig(from, { sdp:{ type:p.pc.localDescription.type, sdp:p.pc.localDescription.sdp } });
      if (callMedia === "video") sig(from, { cam:camOn });
    }
  } else if (d.candidate) {
    if (!p || !p.pc.remoteDescription) { if (p) p.queue.push(d.candidate); return; }
    await p.pc.addIceCandidate(d.candidate).catch(() => {});
  } else if (typeof d.cam === "boolean") {
    tileFor(from).el.classList.toggle("cam-off", !d.cam);
  }
}
function closePeer(name) { const p = peers.get(name); if (p) { try { p.pc.close(); } catch (e) {} peers.delete(name); } removeTile(name); }
function startClock() {
  clearInterval(clockTimer);
  const tick = () => { const s = Math.floor((Date.now() - connectedAt) / 1000); $("callTime").textContent = `${String(Math.floor(s / 60)).padStart(2, "0")}:${String(s % 60).padStart(2, "0")}`; };
  tick(); clockTimer = setInterval(tick, 1000);
}
function hangup() {
  if (ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"call_leave" }));
  endLocal();
}
function endLocal(msg) {
  if (!inCall) return;
  inCall = false;
  for (const n of [...peers.keys()]) closePeer(n);
  for (const n of [...tiles.keys()]) removeTile(n);
  if (localStream) localStream.getTracks().forEach(t => t.stop());
  localStream = null; $("localVid").srcObject = null;
  clearTimeout(aloneTimer); aloneTimer = null; clearInterval(clockTimer); connectedAt = 0;
  $("callView").hidden = true; $("callTime").textContent = "";
  if (wakeLock) { wakeLock.release().catch(() => {}); wakeLock = null; }
  if (msg) toast(msg);
  callKey = null; updateCallBar(); renderHomeSoon();
}
function paintCallBtns() {
  const mic = $("btnMic"), cam = $("btnCam");
  mic.classList.toggle("on", !micOn); mic.querySelector(".round").innerHTML = icon(micOn ? "i-mic" : "i-mic-off"); mic.lastElementChild.textContent = micOn ? "静音" : "已静音";
  cam.classList.toggle("on", !camOn); cam.querySelector(".round").innerHTML = icon(camOn ? "i-video" : "i-video-off"); cam.lastElementChild.textContent = camOn ? "关摄像头" : "开摄像头";
}
$("btnHang").onclick = hangup;
$("btnMic").onclick = () => { micOn = !micOn; localStream && localStream.getAudioTracks().forEach(t => t.enabled = micOn); paintCallBtns(); };
$("btnCam").onclick = () => {
  camOn = !camOn; localStream && localStream.getVideoTracks().forEach(t => t.enabled = camOn);
  $("localVid").hidden = !camOn; for (const n of peers.keys()) sig(n, { cam:camOn }); paintCallBtns();
};
$("btnFlip").onclick = async () => {
  if (!localStream) return;
  const old = localStream.getVideoTracks()[0]; const next = facing === "user" ? "environment" : "user";
  try {
    if (old) old.stop();
    const s = await navigator.mediaDevices.getUserMedia({ video:{ facingMode:{ exact:next }, width:{ ideal:960 }, height:{ ideal:720 } } })
      .catch(() => navigator.mediaDevices.getUserMedia({ video:{ facingMode:next } }));
    const track = s.getVideoTracks()[0]; track.enabled = camOn;
    if (old) localStream.removeTrack(old); localStream.addTrack(track);
    for (const p of peers.values()) { const snd = p.pc.getSenders().find(x => x.track && x.track.kind === "video"); if (snd) await snd.replaceTrack(track); }
    facing = next; $("localVid").srcObject = localStream; $("localVid").classList.toggle("mirror", facing === "user");
  } catch (e) { toast("切换摄像头失败"); }
};
window.addEventListener("pagehide", () => { if (inCall && ws && ws.readyState === 1) ws.send(JSON.stringify({ type:"call_leave" })); });

/* ================= 启动 ================= */
$("nick").value = ls.get("chatName") || "";
draftAvatar = myAvatar; showPreview();
if ($("nick").value.trim()) join();          // 以前进来过：直接进入，不用每次再点
</script>
</body>
</html>
"""

ICON_192 = "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"
ICON_512 = "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"


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
    port = int(os.environ.get("PORT", 8000))   # 云服务器会通过 PORT 告诉我们用哪个端口
    print(f"\n聊天室已启动！")
    print(f"  本机访问:   http://localhost:{port}")
    print(f"  局域网访问: http://{local_ip()}:{port}\n")
    uvicorn.run(app, host="0.0.0.0", port=port, log_level="warning")
