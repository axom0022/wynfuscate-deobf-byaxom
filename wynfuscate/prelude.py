from __future__ import annotations
import re
from .util import balancedparen, i31, luaunescape, numericenv, safeeval, strlit, u32

def stage1strings(src: str):
    m = re.search('local\\s+(\\w+)\\s*=\\s*\\(?\\s*(\\w+)\\[1\\]or\\"\\"\\)', src)
    if not m:
        return None
    chunkvar = m.group(2)
    region = src[:m.start()]
    entries = {}
    tbl = re.search('local\\s+' + re.escape(chunkvar) + '\\s*=\\s*\\{', region)
    if tbl:
        pos = tbl.end()
        entryre = re.compile('\\s*,?\\s*\\[(\\d+)\\]\\s*=\\s*(\\"(?:[^\\"\\\\]|\\\\.)*\\")')
        while True:
            em = entryre.match(src, pos)
            if not em:
                break
            entries[int(em.group(1))] = luaunescape(em.group(2)[1:-1])
            pos = em.end()
        if not entries:
            pos = tbl.end()
            while True:
                ws = re.match('\\s*,?\\s*', src[pos:])
                pos += ws.end()
                sm = strlit.match(src, pos)
                if not sm:
                    break
                entries[len(entries) + 1] = luaunescape(sm.group(1))
                pos = sm.end()
    if not entries:
        return None
    pool = b''.join((entries[k] for k in sorted(entries)))
    env = numericenv(src)
    seed = None
    searchfrom = m.end()
    for cm in re.finditer('local\\s+(\\w+)\\s*=\\s*\\(', src[searchfrom:searchfrom + 4000]):
        expr = balancedparen(src, searchfrom + cm.end() - 1)
        if expr is None:
            continue
        val = safeeval(expr, env)
        if val is not None:
            seed = val % u32
            tail = src[searchfrom + cm.end():searchfrom + cm.end() + 200]
            ik = re.search('IK\\((\\d+),0\\)', tail)
            if ik:
                irm = re.search('Ir\\[' + ik.group(1) + '\\]=(\\d+)', src)
                if irm:
                    seed = (seed + int(irm.group(1))) % i31
            break
    if seed is None:
        return None
    strings = {}
    for sid in range(0, 100000):
        s = stage1one(pool, seed, sid)
        if s is None:
            break
        strings[sid] = s
    return (strings, {'pool_len': len(pool), 'seed': seed})

def stage1one(pm: bytes, seed: int, sid: int):
    try:
        r = 0
        c = 0
        j = seed
        hops = sid
        while hops > 0:
            if r + 2 >= len(pm):
                return None
            s = pm[r] + pm[r + 1] * 256
            t = (j + c * 257 + s % 65536 + 21417) % u32
            t = (t * 1664525 + 1013904223 + c * 40503 + j % 65536 * 11117) % u32
            if t == 0:
                t = (j + 1) % u32
            t = (t * 1664525 + 1013904223 + c * 257 + 1831565813 + s % 65536) % u32
            b0, b1, b2, b3 = (t & 255, t >> 8 & 255, t >> 16 & 255, t >> 24 & 255)
            m6 = pm[r + 2] ^ b0 ^ b1 ^ b2 ^ b3 + c & 255
            r += 3 + m6
            c += 1
            hops -= 1
        if r + 2 >= len(pm):
            return None
        s = pm[r] + pm[r + 1] * 256
        t = (j + c * 257 + s % 65536 + 21417) % u32
        t = (t * 1664525 + 1013904223 + c * 40503 + j % 65536 * 11117) % u32
        if t == 0:
            t = (j + 1) % u32
        t = (t * 1664525 + 1013904223 + c * 257 + 1831565813 + s % 65536) % u32
        b0, b1, b2, b3 = (t & 255, t >> 8 & 255, t >> 16 & 255, t >> 24 & 255)
        ln = pm[r + 2] ^ b0 ^ b1 ^ b2 ^ b3 + c & 255
        if r + 2 + ln >= len(pm):
            return None
        out = bytearray()
        for k in range(1, ln + 1):
            t = (t * 1664525 + 1013904223 + c * 257 + k * 131 + ln * 17 + s % 65536 + 1831565813) % u32
            b0, b1, b2, b3 = (t & 255, t >> 8 & 255, t >> 16 & 255, t >> 24 & 255)
            mask = b0 ^ b1 + k & 255 ^ (b2 ^ b3 + c + ln & 255)
            out.append(pm[r + 2 + k] ^ mask)
        return bytes(out)
    except Exception:
        return None
