from __future__ import annotations
import re

u32 = 1 << 32
i31 = 2147483647
robloxenv = {'vc': 1, 'vK': 1, 'vS': 1, 'vJ': 1, 'vV': 104, 'vg': 1, 'vN': 1, 'gi': 1, 'gq': 1, 'g9': 104, 'g8': 1, 'gZ': 0, 'gY': 0}

def readtext(path: pth) -> str:
    return path.read_text(encoding='utf-8', errors='replace')

def luaunescape(lit: str) -> bytes:
    out = bytearray()
    i, n = (0, len(lit))
    esc = {'n': 10, 't': 9, 'r': 13, 'a': 7, 'b': 8, 'f': 12, 'v': 11, '\\': 92, '"': 34, "'": 39, '\n': 10}
    while i < n:
        c = lit[i]
        if c == '\\' and i + 1 < n:
            i += 1
            if lit[i].isdigit():
                j = i
                while j < n and j < i + 3 and lit[j].isdigit():
                    j += 1
                out.append(int(lit[i:j]) & 255)
                i = j
            else:
                out.append(esc.get(lit[i], ord(lit[i])))
                i += 1
        else:
            out.append(ord(c) & 255)
            i += 1
    return bytes(out)
strlit = re.compile('"((?:[^"\\\\\\n]|\\\\.)*)"')
localstr = re.compile('local\\s+(\\w+)\\s*=\\s*"((?:[^"\\\\\\n]|\\\\.)*)"')

def numericenv(src: str) -> dict:
    env = {}
    for m in re.finditer('local\\s+(\\w+)\\s*=\\s*(0[xX][0-9A-Fa-f]+|\\d+)[,;\\s)]', src):
        env[m.group(1)] = int(m.group(2), 0)
    return env

def safeeval(expr: str, env: dict):
    try:

        def sub(m):
            name = m.group(0)
            if name in env:
                return str(env[name])
            raise KeyError(name)
        cleaned = re.sub('\\b[A-Za-z_]\\w*\\b', sub, expr)
    except KeyError:
        return None
    if not re.fullmatch('[0-9+\\-*/%(). ]+', cleaned):
        return None
    try:
        return int(eval(cleaned, {'__builtins__': {}}, {}))
    except Exception:
        return None

def balancedparen(src: str, openidx: int):
    depth = 0
    for i in range(openidx, len(src)):
        if src[i] == '(':
            depth += 1
        elif src[i] == ')':
            depth -= 1
            if depth == 0:
                return src[openidx + 1:i]
    return None

def printableratio(b: bytes) -> float:
    if not b:
        return 0.0
    ok = sum((1 for c in b if 32 <= c < 127 or c in (9, 10, 13)))
    return ok / len(b)

def b91decode(text: str, alpha: dict) -> bytes:
    out = bytearray()
    dl = -1
    acc = 0
    bits = 0
    for ch in text:
        d = alpha.get(ord(ch))
        if d is None:
            continue
        if dl < 0:
            dl = d
            continue
        dl += d * 91
        acc += dl << bits
        bits += 13 if dl % 8192 > 88 else 14
        while bits >= 8:
            out.append(acc & 255)
            acc >>= 8
            bits -= 8
        dl = -1
    if dl >= 0:
        acc += dl << bits
        bits += 7
        while bits >= 8:
            out.append(acc & 255)
            acc >>= 8
            bits -= 8
    return bytes(out)

def lz77decompress(data: bytes, cap: int) -> bytes:
    out = bytearray()
    i = 0
    while len(out) < cap and i < len(data):
        ctrl = data[i]
        i += 1
        for _ in range(8):
            if len(out) >= cap or i >= len(data):
                break
            bit = ctrl & 1
            ctrl >>= 1
            if bit:
                pz = data[i]
                pw = data[i + 1] if i + 1 < len(data) else 0
                i += 2
                pc = pw >> 4
                dist = pc * 256 + pz
                if pc == 15:
                    pa = data[i] if i < len(data) else 0
                    i += 1
                    dist = pa * 256 + pz
                pm = pw & 15
                ln = pm + 3
                if pm == 15:
                    extra = 0
                    while i < len(data):
                        b = data[i]
                        i += 1
                        extra += b
                        if b != 255:
                            break
                    ln = 18 + extra
                src = len(out) - (dist + 1)
                for k in range(ln):
                    if len(out) >= cap:
                        break
                    out.append(out[src + k] if 0 <= src + k < len(out) else 0)
            else:
                out.append(data[i])
                i += 1
    return bytes(out)

def varint(buf, pos):
    val = 0
    mul = 1
    while True:
        b = buf[pos] if pos < len(buf) else 0
        pos += 1
        val += b % 128 * mul
        if b < 128:
            break
        mul *= 128
    return (val, pos)

def varintstream(data: bytes, limit: int=None) -> list:
    out, i, acc, shift = ([], 0, 0, 0)
    while i < len(data) and (limit is None or len(out) < limit):
        b = data[i]
        i += 1
        acc += b % 128 << shift
        if b < 128:
            out.append(acc)
            acc = 0
            shift = 0
        else:
            shift += 7
    return out

def varintdeltastream(data: bytes, limit: int=None) -> list:
    out, i, acc, shift, total = ([], 0, 0, 0, 0)
    while i < len(data) and (limit is None or len(out) < limit):
        b = data[i]
        i += 1
        acc += b % 128 << shift
        if b < 128:
            total += acc
            out.append(total)
            acc = 0
            shift = 0
        else:
            shift += 7
    return out
