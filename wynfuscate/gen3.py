from __future__ import annotations

cu = 4294967296
cp = 2147483647
e4c = 0x27220AA6 - 0x11
k1c = (0x45D5EDE + 0x4064) - 7
k2c = (0x27D46E65 + 31952) - 8
e5seed = 1259955853
b85alpha = 'mki7MKt[2=>cV14)aveEQogHSq5w8CIGBA.n<fWb?*F#9plPyX@T]LZ-zxO{Y:0%J/u3rhRj6}s$U^&(+d!DN'
b85digit = {ord(ch): i for i, ch in enumerate(b85alpha)}
b85char = {i: ch for i, ch in enumerate(b85alpha)}
widths = {207: 8, 202: 8, 201: 8, 224: 8, 167: 8, 162: 8, 163: 8, 183: 8, 178: 8,
          177: 8, 180: 8, 179: 8, 190: 8, 186: 8, 185: 8, 188: 8, 187: 8, 130: 8,
          129: 8, 132: 8, 131: 8, 142: 8, 141: 8, 144: 8, 139: 8, 158: 8, 104: 8,
          100: 8, 105: 8, 115: 8, 126: 8, 125: 8, 128: 8, 127: 8, 122: 8, 124: 8,
          123: 8, 72: 8, 71: 8, 66: 8, 80: 8, 79: 8, 86: 8, 85: 8, 88: 8, 87: 8,
          82: 8, 81: 8, 84: 8, 83: 8, 94: 8, 96: 8, 44: 8, 43: 8, 53: 8, 56: 8,
          55: 8, 50: 8, 49: 8, 52: 8, 51: 8, 62: 8, 61: 8, 64: 8, 63: 8, 58: 8,
          57: 8, 60: 8, 59: 8, 6: 8, 5: 8, 8: 8, 7: 8, 2: 8, 1: 8, 4: 8, 3: 8,
          14: 8, 16: 8, 15: 8, 10: 8, 9: 8, 12: 8, 11: 8, 21: 9, 24: 9, 23: 9,
          18: 8, 17: 8, 20: 8, 19: 8, 30: 8, 29: 8, 32: 8, 31: 8, 26: 8, 25: 8,
          28: 8, 27: 8, 230: 8, 229: 8, 232: 8, 231: 8, 238: 8, 237: 8, 240: 8,
          239: 8, 248: 8, 247: 8}


def xop(a, b):
    return (int(a) & 0xFFFFFFFFFFFFFFFF) ^ (int(b) & 0xFFFFFFFFFFFFFFFF)


def dcmul(a, b):
    return (a * b) % cu


def rotl(x, s):
    x %= cu
    s %= 32
    if s == 0:
        return x
    return ((x << s) % cu + (x >> (32 - s))) % cu


def e4(v, k):
    return xop(v, xop(k, e4c))


def e5(e0, lh):
    cg = xop(e5seed, e0) % cu
    cg = (dcmul(cg, k1c) + dcmul(lh, k2c)) % cu
    cg = rotl(cg, 7)
    cg = xop(cg, cg >> 15) % cu
    cg = dcmul(cg, 2246822507) % cu
    cg = xop(cg, cg >> 13) % cu
    return cg


def idfn(bd, l5, ii, ib, iy, seed, iq):
    ia = xop(xop(xop(l5 * 32, ii * 2048), ib * 131072), iy * 8388608)
    ic = (xop(bd, seed) + ia + iq) % cu
    return (dcmul(rotl(ic, 7), k1c) + k2c) % cu


def dl(w):
    ex = 1701747752
    mix = (w * 40503) % cp
    bias = (2856 + 548 * 7 + 5161 % 97) % cp
    cur = (xop(ex, mix) + bias) % cp
    return (cur * 48271) % cp


def varint(data, pos):
    v = 0
    m = 1
    while True:
        b = data[pos] if pos < len(data) else 0
        pos += 1
        v += (b % 128) * m
        if b < 128:
            return v, pos
        m *= 128


def b85encode(raw):
    out = []
    for i in range(0, len(raw) - len(raw) % 4, 4):
        g = (raw[i] << 24) | (raw[i + 1] << 16) | (raw[i + 2] << 8) | raw[i + 3]
        ds = []
        for _ in range(5):
            ds.append(g % 85)
            g //= 85
        out.extend(b85char[d] for d in reversed(ds))
    rem = len(raw) % 4
    if rem:
        g = 0
        for i in range(len(raw) - rem, len(raw)):
            g = (g << 8) | raw[i]
        g <<= 8 * (4 - rem)
        ds = []
        for _ in range(5):
            ds.append(g % 85)
            g //= 85
        out.extend(b85char[d] for d in reversed(ds[:rem + 1]))
    return ''.join(out)


def b85bytes(s):
    out = bytearray()
    for i in range(0, len(s), 5):
        g = 0
        for j in range(5):
            g = g * 85 + b85digit.get(ord(s[i + j]) if i + j < len(s) else 0, 0)
        out.extend(((g >> 24) & 255, (g >> 16) & 255, (g >> 8) & 255, g & 255))
    return bytes(out)


def packedbyte(s, idx):
    g = 0
    base = (idx // 4) * 5
    for j in range(5):
        g = g * 85 + b85digit.get(ord(s[base + j]) if base + j < len(s) else 0, 0)
    return (g >> (8 * (3 - idx % 4))) & 255


def u32of(s, i, raw4):
    bs = [ord(s[i + j]) if raw4 else packedbyte(s, i + j) for j in range(4)]
    return bs[0] + (bs[1] << 8) + (bs[2] << 16) + (bs[3] << 24)


class gen3proto:
    pass


def parsev52(data, envkey):
    pos = 5
    nprotos, pos = varint(data, pos)
    protos = []
    for pid in range(nprotos):
        p = gen3proto()
        p.pid = pid
        n, pos = varint(data, pos)
        p.n = n
        p.a, pos = varint(data, pos)
        p.b, pos = varint(data, pos)
        p.c, pos = varint(data, pos)
        pu, pos = varint(data, pos)
        px, pos = varint(data, pos)
        p.marks = None
        if px > 0:
            acc = 0
            mk = {}
            for _ in range(px):
                d, pos = varint(data, pos)
                acc += d
                mk[acc] = True
            p.marks = mk
        p.numparams = data[pos]
        p.x8761 = data[pos + 1]
        p.vararg = data[pos + 2] == 1
        nup = data[pos + 3]
        pos += 4
        p.upvals = []
        for _ in range(nup):
            p.upvals.append((data[pos] == 1, data[pos + 1]))
            pos += 2
        p.ops = list(data[pos:pos + n])
        pos += n
        l1 = 0
        p.m2130 = {}
        p.m1850 = {}
        for lx in range(1, n + 1):
            p.m2130[lx] = l1
            p.m1850[l1] = lx
            l1 += widths.get(p.ops[lx - 1], 4)
        wq, pos = varint(data, pos)
        p.packed = b85encode(bytes(data[pos:pos + wq]))
        pos += wq
        wi, pos = varint(data, pos)
        acc = 0
        p.groups = {}
        for lx in range(wi):
            d, pos = varint(data, pos)
            acc += d
            p.groups[acc] = True
        p.gstarts = dict(p.groups)
        p.g1089 = []
        for _ in range(wi):
            v, pos = varint(data, pos)
            p.g1089.append(v)
        p.g7617 = list(data[pos:pos + wi])
        pos += wi
        pn = data[pos]
        pos += 1
        p.secrets = pn != 0
        if p.secrets:
            pj, pos = varint(data, pos)
            pz, pos = varint(data, pos)
            pt, pos = varint(data, pos)
            p.k5726 = pj
            p.iq = xop(pz, envkey) % cu
            p.k4722 = xop(pt, envkey) % cu
            p.init2041 = xop(pj, envkey) % cu
            c3, pos = varint(data, pos)
            p.s1251 = ''.join(chr(b) for b in data[pos:pos + c3])
            pos += c3
            c9, pos = varint(data, pos)
            p.s1952 = ''.join(chr(b) for b in data[pos:pos + c9]) if c9 else None
            pos += c9
            p5, pos = varint(data, pos)
            p0, pos = varint(data, pos)
            p.s2481 = None
            p.n8276 = 0
            if p5 > 0 and p0 > 0:
                p.s2481 = ''.join(chr(b) for b in data[pos:pos + p0])
                p.n8276 = p5
            pos += p0
        else:
            p.k5726 = 0
            p.iq = 0
            p.k4722 = 0
            p.init2041 = 0
            p.s1251 = None
            p.s1952 = None
            p.s2481 = None
            p.n8276 = 0
        wu, pos = varint(data, pos)
        p.jumps = {}
        if wu > 0:
            ww = 5231 + ((6928 + pid * 211) % 8209)
            wg = 7411 + ((2770 + pid * 397) % 12301)
            wj = 23 + ((3234544013 + pid * 149 + 37) % 1009)
            ws = 43 + (((1060423282 - 1060423282 % 1009) // 1009 + pid * 269 + 83) % 1013)
            wp = ww + wj
            wo = wg + ws
            for _ in range(wu):
                wt, pos = varint(data, pos)
                wr, pos = varint(data, pos)
                p.jumps[wt - wp] = wr - wo
        wx = xop(1701747752, 351478) % cp
        pb = dl(wx) % cp or 1
        wf = xop(pb, pid) % cp
        wr = dl(wf) % cp or 1
        wh = ((pid + 1) * 2654435761) % cp
        wn = ((pid + 1) * 131 + 17) % cp
        wu2 = xop(xop(xop(pb, envkey), wh), wn) % cp
        wv = dl(wu2) % cp or 1
        wa = (pu - wv) % cp
        p.key7194 = 0 if wa != wr else wa
        p.bds = None
        p.seeds = None
        if p.secrets and 0 not in p.gstarts:
            c3b = (n + 15) // 16
            if p.s1251 is not None:
                raw = len(p.s1251) == c3b * 4
                p.bds = [e4(u32of(p.s1251, (i - 1) * 4, raw), p.k4722) for i in range(1, c3b + 1)]
            if p.s1952:
                raw = len(p.s1952) == n * 4
                p.seeds = [u32of(p.s1952, (i - 1) * 4, raw) for i in range(1, n + 1)]
        p.cols = {c: {} for c in (4998, 8727, 5102, 8959, 1228, 1514, 6151, 6134)}
        p.x7059 = {}
        p.after = pos
        protos.append(p)
    return protos, pos


def drive(p):
    if not p.secrets or p.bds is None:
        return False
    bd = p.bds[0]
    last = 0
    seeds = p.seeds if p.seeds is not None else {}
    for pc in range(1, p.n + 1):
        if pc == 1:
            bd = p.bds[0]
        elif pc != last + 1:
            bd = catchup(p, pc)
        seed = seeds.get(pc)
        if seed is None:
            seed = e5(p.pid, pc - 1)
            seeds[pc] = seed
        i2 = xop(bd, seed)
        sh = (5, 0, 9, 17, 21, 25, 3, 11)
        vals = []
        for j in range(8):
            b = packedbyte(p.packed, (pc - 1) * 8 + j)
            vals.append(xop(b, rotl(i2, sh[j]) % 256))
        cols = p.cols
        cols[4998][pc] = vals[0]
        cols[8727][pc] = vals[1]
        cols[5102][pc] = vals[2]
        cols[8959][pc] = vals[3]
        cols[1228][pc] = vals[4]
        cols[1514][pc] = vals[5]
        cols[6151][pc] = vals[6]
        cols[6134][pc] = vals[7]
        bd = idfn(bd, vals[0], vals[1], vals[2], vals[3], seed, p.iq)
        last = pc
    if p.s2481 and p.n8276 > 0:
        kd = p.n8276
        ki = kd * 5
        ki += (4 - ki % 4) % 4
        raw = len(p.s2481) == ki
        for lx in range(kd):
            o = lx * 5
            b0 = ord(p.s2481[o]) if raw else packedbyte(p.s2481, o)
            b1 = ord(p.s2481[o + 1]) if raw else packedbyte(p.s2481, o + 1)
            b2 = ord(p.s2481[o + 2]) if raw else packedbyte(p.s2481, o + 2)
            b3 = ord(p.s2481[o + 3]) if raw else packedbyte(p.s2481, o + 3)
            b4 = ord(p.s2481[o + 4]) if raw else packedbyte(p.s2481, o + 4)
            p.x7059[b0 + (b1 << 8) + (b2 << 16) + (b3 << 24) + 1] = b4
    return True


def catchup(p, pc):
    ik = (pc - 1) // 16 + 1
    iw = (ik - 1) * 16 + 1
    im = p.bds[ik - 1] if ik - 1 < len(p.bds) else p.bds[-1]
    if iw >= pc:
        return im
    bd = im
    for g in range(iw, pc):
        seed = (p.seeds or {}).get(g)
        if seed is None:
            seed = e5(p.pid, g - 1)
        i2 = xop(bd, seed)
        sh = (5, 0, 9, 17, 21, 25, 3, 11)
        vals = []
        for j in range(8):
            b = packedbyte(p.packed, (g - 1) * 8 + j)
            vals.append(xop(b, rotl(i2, sh[j]) % 256))
        bd = idfn(bd, vals[0], vals[1], vals[2], vals[3], seed, p.iq)
    return bd
