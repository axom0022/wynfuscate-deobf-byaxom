from __future__ import annotations
import re
from .util import luaunescape, strlit

b85alphabet = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ.-:+=^!/*?&<>()[]{}@%$#'

def unpackenhancedvm(src: str):
    m61 = re.search('local\\s+\\w+\\s*=\\s*\\{(\\d+(?:\\s*,\\s*\\d+){80,})\\}', src)
    if not m61:
        return None
    perm = [int(x) for x in m61.group(1).split(',')]
    arrstart = src.find('{', m61.end())
    if arrstart < 0:
        return None
    chunks = []
    pos = arrstart + 1
    while True:
        ws = re.match('\\s*,?\\s*', src[pos:])
        pos += ws.end()
        sm = strlit.match(src, pos)
        if not sm:
            break
        chunks.append(luaunescape(sm.group(1)).decode('latin-1'))
        pos = sm.end()
    if len(chunks) < len(perm):
        return None
    ordered = [None] * len(perm)
    for i in range(len(perm)):
        ordered[perm[i] - 1] = chunks[i]
    u6 = ''.join((x for x in ordered if x is not None))
    r7 = u6[25:]
    map85 = {c: i for i, c in enumerate(b85alphabet)}
    raw = bytearray()
    for i in range(0, len(r7), 5):
        h = 0
        for k in range(5):
            if i + k >= len(r7):
                break
            h = h * 85 + map85.get(r7[i + k], 0)
        raw.append(h // 16777216 % 256)
        raw.append(h // 65536 % 256)
        raw.append(h // 256 % 256)
        raw.append(h % 256)
    return lzmadecode(bytes(raw))

def lzmadecode(a1: bytes):
    if len(a1) < 10:
        return None
    outlen2 = a1[0] | a1[1] << 8 | a1[2] << 16 | a1[3] << 24
    if not 0 < outlen2 <= 268435456:
        return None
    pos = 4

    def byte():
        nonlocal pos
        b = a1[pos] if pos < len(a1) else 0
        pos += 1
        return b
    rng = 4294967295
    code = 0
    for _ in range(5):
        code = code * 256 + byte()
    probs = [1024] * 8129
    top = 1 << 24

    def bit(i):
        nonlocal rng, code
        if rng < top:
            rng *= 256
            code = code * 256 + byte()
        p = probs[i]
        bound = rng // 2048 * p
        if code < bound:
            rng = bound
            probs[i] = p + (2048 - p) // 32
            return 0
        rng -= bound
        code -= bound
        probs[i] = p - p // 32
        return 1

    def tree(a, n):
        m = 1
        for _ in range(n):
            m = m + m + bit(a + m)
        return m - (1 << n)

    def bittree(a, n, c):
        m = 1
        for _ in range(n):
            if bit(a + c) == 0:
                c += m
                m += m
            else:
                m += m
                c += m
        return c - m

    def direct(a, b):
        nonlocal rng, code
        for _ in range(a):
            if rng < top:
                rng *= 256
                code = code * 256 + byte()
            rng //= 2
            b += b
            if code >= rng:
                code -= rng
                b += 1
        return b
    g92, a72, p3, v4, g9, j2 = (0, 128, 384, 896, 1408, 1664)
    q9, m5, p9, e3, b9, l6 = (1680, 1692, 1704, 1716, 1728, 1984)

    def lendec(a):
        if bit(a + 1) == 0:
            return tree(a + 1, 3)
        if bit(a + 1 + 8) == 0:
            return tree(a + 1 + 8, 3) + 8
        return tree(a + 1 + 256, 8) + 16
    out = bytearray()
    i3 = 0
    q5 = 0
    l9 = m8 = w1 = t8 = 1
    z9 = 0
    while i3 < outlen2:
        if bit(g9 + 1 + q5) == 0:
            s0 = l6 + 1 + (z9 >> 5) * 768
            b92 = 1
            if q5 < 7:
                while b92 < 256:
                    b92 = b92 + b92 + bit(s0 + b92)
            else:
                a7 = out[i3 - l9]
                n1 = 256
                while b92 < 256:
                    a7 = a7 * 2 % 512
                    a3 = n1
                    if n1 != 0:
                        n1 = 256 if a7 >= 256 else 0
                    m0 = s0 + n1 + a3 + b92
                    if bit(m0) == 0:
                        b92 = b92 + b92
                        if a3 != 0:
                            n1 = 256 - n1
                    else:
                        b92 = b92 + b92 + 1
            b92 %= 256
            out.append(b92)
            z9 = b92
            i3 += 1
            q5 = 0 if q5 < 4 else q5 - 3 if q5 < 10 else q5 - 6
        else:
            f1 = 0
            t4 = False
            if bit(q9 + 1 + q5) == 0:
                q5 += 12
                f1 = lendec(v4)
            else:
                if bit(m5 + 1 + q5) == 0:
                    if bit(a72 + 1 + q5) == 0:
                        c12 = out[i3 - l9]
                        out.append(c12)
                        z9 = c12
                        i3 += 1
                        q5 = 9 if q5 < 7 else 11
                        t4 = True
                else:
                    if bit(p9 + 1 + q5) == 0:
                        m4 = m8
                    else:
                        if bit(e3 + 1 + q5) == 0:
                            m4 = w1
                        else:
                            m4 = t8
                            t8 = w1
                        w1 = m8
                    m8 = l9
                    l9 = m4
                if not t4:
                    q5 = 8 if q5 < 7 else 11
                    f1 = lendec(p3)
            if not t4:
                if q5 >= 12:
                    m4 = tree(b9 + 1 + (f1 if f1 < 4 else 3) * 64, 6)
                    if m4 >= 4:
                        c4 = m4
                        q6 = c4 // 2 - 1
                        m4 = 2 + c4 % 2
                        if c4 < 14:
                            m4 = m4 * (1 << q6)
                            m4 = bittree(g92 + 1, q6, m4 + 1)
                        else:
                            m4 = direct(q6 - 4, m4)
                            m4 = m4 * 16 + bittree(j2 + 1, 4, 1)
                    t8, w1, m8 = (w1, m8, l9)
                    l9 = m4 + 1
                    q5 = 7 if q5 < 19 else 10
                f1 += 2
                for _ in range(f1):
                    c12 = out[i3 - l9]
                    out.append(c12)
                    z9 = c12
                    i3 += 1
                    if i3 >= outlen2:
                        break
    return out.decode('latin-1')
