from __future__ import annotations
import hashlib
import re
import struct
from .util import b91decode, i31, localstr, luaunescape, lz77decompress, numericenv, printableratio, robloxenv, safeeval, u32, varint, varintdeltastream, varintstream
from .prelude import stage1strings
from .semant import extractcond, extractje, extractjunkops, extractukbias, extractuyur
from . import gen3

class vmdeobf:

    def __init__(self, src: str):
        self.src = src
        self.warnings = []
        self.variant = 'B' if 'ComputeStringHash' in src else 'A'
        self.strings = {}
        self.protos = []
        self.handlers = {}
        self.colnames = {}
        self.colids = []
        self.inlinemap = []
        self.wptversion = None

    def findmega(self):
        best = None
        for m in localstr.finditer(self.src):
            if len(m.group(2)) > 3000 and (best is None or len(m.group(2)) > len(best.group(2))):
                best = m
        return best

    def tablealphabets(self):
        out = []
        for m in re.finditer('\\{(\\[\\d+\\]=0,(?:\\[\\d+\\]=\\d+,?)+)\\}', self.src):
            d = {int(k): int(v) for k, v in re.findall('\\[(\\d+)\\]=(\\d+)', m.group(1))}
            if len(d) >= 91:
                out.append(d)
        return out

    def stringalphabets(self):
        out = []
        for m in re.finditer('="([^"]{91})"for\\s+\\w+=1,91\\s+do', self.src):
            out.append({ord(c): i for i, c in enumerate(m.group(1))})
        return out

    def probevalues(self):
        strings = {}
        s1 = stage1strings(self.src)
        if s1:
            strings = {k: (v if isinstance(v, str) else v.decode('utf-8', 'replace'))
                       for k, v in s1[0].items()}
        env = {}
        for m in re.finditer(r'local (\w+)=\((\w+)>0 and \2<=49157\)and 1 or 0', self.src):
            env[m.group(1)] = 1
        for m in re.finditer(r'(\w+)=\((\w+)\[(\w+)\((\d+)\)\]\*31\+\2\[\3\((\d+)\)\]\*17\+\2\[\3\((\d+)\)\]\*13\)', self.src):
            if [strings.get(int(m.group(i))) for i in (4, 5, 6)] == ['X', 'Y', 'Z']:
                env[m.group(1)] = 104
        for m in re.finditer(r'local (\w+)=\((\w+)~=nil and [^;]{0,260}?and 1 or 0', self.src):
            d = re.search(r'local %s=[^;]{0,240}' % re.escape(m.group(2)), self.src)
            if d and re.search(r'game|Instance|Vector3int16|workspace|Enum|Players', d.group(0)):
                env[m.group(1)] = 1
        for m in re.finditer(r'local (\w+)=0', self.src):
            w = self.src[m.end():m.end() + 700]
            g = re.search(r'then %s=1 end' % m.group(1), w)
            if g and re.search(r'==[A-Za-z]\w*\[[A-Za-z]\w*\(', w[:g.start()]):
                env.setdefault(m.group(1), 1)
        return env

    def extractenvchain(self):
        for mm in re.finditer('(\\w+)=\\((\\w+)%2147483647\\)', self.src):
            acc = mm.group(1)
            if mm.group(2) != acc and (not mm.group(2).isdigit()):
                pass
            pat = re.compile(re.escape(acc) + '=\\(' + re.escape(acc) + '\\*48271\\+((?:\\([^+()]+\\)|[^+()]+))\\+81\\)%2147483647')
            steps = pat.findall(self.src)
            if len(steps) < 2:
                continue
            init = None
            win = self.src[max(0, mm.start() - 1500):mm.start()]
            for im in re.finditer('local\\s+(\\w+)\\s*=\\s*(\\d+)', win):
                if im.group(1) == mm.group(2):
                    init = int(im.group(2))
            if init is None:
                im2 = re.search('local\\s+\\w+\\s*=\\s*(\\d+)[^;]*' + re.escape(mm.group(2)), win)
                init = int(im2.group(1)) if im2 else None
            if init is None:
                continue
            env = numericenv(self.src)
            env.update(robloxenv)
            env.update(self.probevalues())
            vals = []
            for st in steps:
                v = safeeval(st, env)
                if v is None:
                    v = safeeval(st.strip('()'), env)
                if v is None:
                    self.warnings.append(f'chain step {st!r} not evaluable; assuming Roblox probes')
                    v = 104
                vals.append(v)
            x = init % i31
            for v in vals:
                x = (x * 48271 + v + 81) % i31
            return x
        return None

    def mixerparams(self):
        mm = re.search('function\\((\\w+)\\)local\\s+\\w+\\s*=\\s*n8\\[zk\\[(\\d+)\\]\\]local\\s+\\w+\\s*=\\s*\\(\\(\\1\\*40503\\)%n8\\[zk\\[(\\d+)\\]\\]\\)', self.src)
        if mm:
            ids = {}
            for am in re.finditer('n8\\[zk\\[(\\d+)\\]\\]\\s*=\\s*(\\d+)\\b', self.src):
                ids.setdefault(am.group(1), int(am.group(2)))
            lzid = mm.group(2)
            cm = re.search('n8\\[zk\\[' + lzid + '\\]\\]=\\(\\(\\w+\\(n8\\[zk\\[(\\d+)\\]\\],n8\\[zk\\[(\\d+)\\]\\]\\)\\+n8\\[zk\\[(\\d+)\\]\\]\\)', self.src)
            pm = re.search('n8\\[zk\\[(\\d+)\\]\\]\\+\\(n8\\[zk\\[(\\d+)\\]\\]\\*7\\)\\+\\(n8\\[zk\\[(\\d+)\\]\\]%97\\)', self.src)
            if cm and pm:
                try:
                    a, b, c = (ids[cm.group(1)], ids[cm.group(2)], ids[cm.group(3)])
                    lz = ((a ^ b) + c) % i31
                    pp, q, rr = (ids[pm.group(1)], ids[pm.group(2)], ids[pm.group(3)])
                    return (lz, (pp + q * 7 + rr % 97) % i31)
                except KeyError:
                    pass
        gm = re.search('function\\((\\w+)\\)local\\s+\\w+\\s*=\\s*(\\w+)\\[(\\w+)\\[(\\d+)\\]\\]local\\s+\\w+\\s*=\\s*\\(\\(\\1\\*40503\\)%', self.src)
        if gm:
            tref = re.escape(gm.group(2)) + '\\[' + re.escape(gm.group(3)) + '\\[(\\d+)\\]\\]'
            vals = {}
            for am in re.finditer(tref.replace('(\\d+)', '(\\\\d+)') + '\\s*=\\s*(\\d+)\\b', self.src):
                vals.setdefault(am.group(1), int(am.group(2)))
            lzid = gm.group(4)
            lzdef = re.search(re.escape(gm.group(2)) + '\\[' + re.escape(gm.group(3)) + '\\[' + lzid + '\\]\\]=\\(\\(\\w+\\(' + tref + ',' + tref + '\\)\\+' + tref + '\\)', self.src)
            if lzdef:
                try:
                    a = vals[lzdef.group(1)]
                    b = vals[lzdef.group(2)]
                    c = vals[lzdef.group(3)]
                    lz = ((a ^ b) + c) % i31
                    pm = re.search('local\\s+\\w+\\s*=\\s*\\((\\d+)\\+\\((\\d+)\\*7\\)\\+\\((\\d+)%97\\)\\)%', self.src)
                    if pm:
                        return (lz, (int(pm.group(1)) + int(pm.group(2)) * 7 + int(pm.group(3)) % 97) % i31)
                    pm2 = re.search(tref.replace('(\\d+)', '(\\\\d+)') + '\\+\\(' + tref + '\\*7\\)\\+\\(' + tref + '%97\\)', self.src)
                    if pm2:
                        pp, q, rr = (vals[pm2.group(1)], vals[pm2.group(2)], vals[pm2.group(3)])
                        return (lz, (pp + q * 7 + rr % 97) % i31)
                except KeyError:
                    pass
        m = re.search('function\\(\\w+\\)local\\s+\\w+\\s*=\\s*\\(\\w+\\((\\d+),(\\d+)\\)\\+(\\d+)\\)%\\w+', self.src)
        if m:
            lz = ((int(m.group(1)) ^ int(m.group(2))) + int(m.group(3))) % i31
            pm = re.search('local\\s+\\w+\\s*=\\s*\\((\\d+)\\+\\((\\d+)\\*7\\)\\+\\((\\d+)%97\\)\\)%\\w+', self.src)
            if pm:
                return (lz, (int(pm.group(1)) + int(pm.group(2)) * 7 + int(pm.group(3)) % 97) % i31)
        return None

    def wptkey(self, mixer, envkey):
        c0 = c1 = None
        for guard in re.finditer('%256==0 then \\w+=\\w+\\+1 end return', self.src):
            window = self.src[max(0, guard.start() - 700):guard.start()]
            c0 = re.search('\\((\\d{7,10}),(\\d{3,7})\\)%', window)
            c1 = re.search('\\([A-Za-z_]\\w*,(\\d{4,9})\\)%', window)
            if c0 and c1:
                break
        if not (c0 and c1):
            return None
        k0 = (int(c0.group(1)) ^ int(c0.group(2))) % i31
        k1 = mixer(k0) % i31 or 1
        k2 = mixer((k1 ^ int(c1.group(1))) % i31) % i31 or 1
        k3 = mixer((k1 ^ k2 ^ envkey) % i31) % i31
        ik = re.search('IK\\((\\d+),0\\)', window)
        if ik:
            irm = re.search('Ir\\[' + ik.group(1) + '\\]=(\\d+)', self.src)
            if irm:
                k3 = (k3 + int(irm.group(1))) % i31
        if k3 % 256 == 0:
            k3 += 1
        return (k1, k3)

    def strseedconsts(self):
        m = re.search(r'\(\w+\*\w+\)\+\(\w+\*\d+\)\+(\d+)\+(\d+)\+\(\(0%65536\)\*17\)\+21417', self.src)
        if m:
            return (int(m.group(1)), int(m.group(2)))
        return (20130, 53393) if self.variant == 'A' else (7271, 33364)

    def strhashvals(self):
        m = re.search(r'local function (\w+)\((\w+)\)local (\w+)=0 if \w+\(\2\)~=.string.then return 0 end local (\w+)=#\2 for \w+=1,\4 do \3=\(\3\*(\d+)\+\(\w+\.byte\(\2,\w+\)or 0\)\+(\d+)\)%cp end if \4>0 then \3=\(\3\+\4\*(\d+)\+\(\w+\.byte\(\2,1\)or 0\)\*(\d+)\+\(\w+\.byte\(\2,\4\)or 0\)\*(\d+)\)%cp end return \3 end', self.src)
        if not m:
            return None
        return (m.group(1), tuple(int(x) for x in m.groups()[4:]))

    def hashstring(self, s, hc):
        a, b, c, d, e = hc
        raw = s.encode('latin-1')
        h = 0
        for ch in raw:
            h = (h * a + ch + b) % i31
        n = len(raw)
        if n > 0:
            h = (h + n * c + raw[0] * d + raw[-1] * e) % i31
        return h

    def luaprobechain(self):
        m = re.search(r'local (\w+),(\w+)=pcall,type local (\w+)=0', self.src)
        if not m:
            return 0
        acc = m.group(3)
        endm = re.search(r'\w+=\(\w+\+' + re.escape(acc) + r'\)%cU', self.src[m.start():m.start() + 6000])
        if not endm:
            return 0
        region = self.src[m.start():m.start() + endm.start()]
        total = 0
        found = False
        probe = r'\(\(\w+ and \w+==[^)]*\)and (\d+) or 0\)'
        pata = re.compile(re.escape(acc) + r'=\(' + re.escape(acc) + r'\*(\d+)\+' + probe + r'\+(\d+)\)%cp')
        patb = re.compile(re.escape(acc) + r'=\(\(\(' + re.escape(acc) + r'\*(\d+)\+(\d+)\)%cp\)\+' + probe + r'\)%cp')
        patc = re.compile(re.escape(acc) + r'=\(' + re.escape(acc) + r'\*(\d+)\+(\d+)\+' + probe + r'\)%cp')
        marks = []
        for rx in (pata, patb, patc):
            for sm in rx.finditer(region):
                marks.append((sm.start(), sm.groups()))
        marks.sort()
        for pos, g in marks:
            found = True
            if len(g) == 3:
                total = (total * int(g[0]) + int(g[1]) + int(g[2])) % i31
            else:
                total = ((total * int(g[0]) + int(g[1])) % i31 + int(g[2])) % i31
        return total if found else 0

    def robloxfactchain(self):
        hv = self.strhashvals()
        if not hv:
            return 0
        hconsts = hv[1]
        strings = {}
        s1 = stage1strings(self.src)
        if s1:
            strings = {k: (v if isinstance(v, str) else v.decode('utf-8', 'replace'))
                       for k, v in s1[0].items()}
        gm = re.search(r'local (\w+)=\w+\(ii\((\d+)\)\)or\(game~=nil and game or nil\)', self.src)
        im = re.search(r'local (\w+)=\w+\(ii\((\d+)\)\)or\(Instance~=nil and Instance or nil\)', self.src)
        if not gm or not im:
            return 0
        if strings.get(int(gm.group(2))) != 'game' or strings.get(int(im.group(2))) != 'Instance':
            return 0
        bm = re.search(r'do local (\w+)=0 \w+=\w+ and \w+\[ii\(\d+\)\]or nil', self.src)
        if not bm:
            return 0
        acc = bm.group(1)
        begin = bm.start()
        endm = re.search(r'\w+=\(\w+\+' + re.escape(acc) + r'\)%cU', self.src[begin:begin + 9000])
        if not endm:
            return 0
        region = self.src[begin:begin + endm.start()]
        steppat = re.compile(re.escape(acc) + r'=\(' + re.escape(acc) + r'\*(\d+)\+(\w+)\+(\d+)\)%cp')
        steps = list(steppat.finditer(region))
        if not steps:
            return 0
        total = 0
        lastcls = None
        prev = 0
        for sm in steps:
            seg = region[prev:sm.start()]
            prev = sm.end()
            ids = [strings.get(int(x)) for x in re.findall(r'ii\((\d+)\)', seg)]
            if '*31' in seg and '*13' in seg:
                v = 104
            elif 'floor' in seg:
                v = 497
            elif 'GetService' in ids:
                svc = None
                for x in ids:
                    if x not in ('GetService', 'ClassName', 'Name', 'new'):
                        svc = x
                v = self.hashstring(svc or 'Players', hconsts)
            elif 'new' in ids:
                cls = None
                for x in ids:
                    if x not in ('new', 'ClassName', 'Name', 'game', 'Instance'):
                        cls = x
                if cls:
                    lastcls = cls
                v = self.hashstring(lastcls or 'Folder', hconsts)
            elif 'ClassName' in ids:
                v = self.hashstring('DataModel', hconsts)
            elif 'Name' in ids:
                v = self.hashstring(lastcls or 'Folder', hconsts)
            else:
                v = 0
            total = (total * int(sm.group(1)) + v + int(sm.group(3))) % i31
        return total

    def stringkey(self, envkey):
        m = re.search('\\(\\(\\(\\((\\d+)-2309737967\\)', self.src)
        if not m:
            return None
        base = int(m.group(1))
        key = (((base - 2309737967) % u32 + 270544960) % u32 - 270544960) % u32
        key = (key + envkey) % u32
        tt = 0
        if self.variant != 'B':
            key = (key + self.luaprobechain() + self.robloxfactchain()) % u32
        if self.variant == 'B':
            shaanchor = self.src.find('ComputeStringHash')
            head = self.src[:shaanchor] if shaanchor >= 0 else self.src
            t7m = None
            for cand in re.finditer('local\\s+\\w+\\s*=\\s*\\(\\((\\d+)\\*(\\d+)\\+(\\d+)\\*(\\d+)\\+(\\d+)\\)', head):
                t7m = cand
            if not t7m:
                return None
            t7 = (int(t7m.group(1)) * int(t7m.group(2)) + int(t7m.group(3)) * int(t7m.group(4)) + int(t7m.group(5))) % u32
            key = (key + t7) % u32
            ujm = None
            for cand in re.finditer('local\\s+\\w+\\s*=\\s*\\((0x[0-9A-Fa-f]+)-(\\d+)\\)', head):
                ujm = cand
            uj = (int(ujm.group(1), 16) - int(ujm.group(2))) % u32 if ujm else 0
            shaargs = [456, 30, 291, 8252, 2836]
            hm = re.search('ComputeStringHash', self.src)
            if hm:
                win = self.src[hm.start() - 200:hm.start()]
                found = re.findall('\\w\\((\\d+)\\)', win)
                if len(found) >= 5:
                    shaargs = [int(x) for x in found[-5:]]
            blob = b''.join((struct.pack('<I', v % u32) for v in [key, t7, uj] + shaargs))
            t0, t6 = struct.unpack('<II', hashlib.sha256(blob).digest()[:8])
            key = (key + t0) % u32
            tt = t6
        return (key, tt)

    def blockconstants(self):
        anchor = self.src.find('=2166136261')
        if anchor < 0:
            return None
        nums = [int(m.group(1)) for m in re.finditer('=(\\d{5,12})\\b', self.src[anchor:anchor + 3000])]
        nums = [n for n in nums if n not in (2166136261, 16777619)]
        if len(nums) < 3:
            return None
        k1, k2, k3 = (nums[0], nums[1], nums[2])
        k4 = None
        m = re.search('=zn\\(n8\\[zk\\[(\\d+)\\]\\],zn\\(', self.src) or re.search('=O6\\(O9\\[IF\\[(\\d+)\\]\\],O6\\(', self.src)
        if m:
            am = re.search('n8\\[zk\\[' + m.group(1) + '\\]\\]\\s*=\\s*(\\d+)', self.src) or re.search('O9\\[IF\\[' + m.group(1) + '\\]\\]\\s*=\\s*(\\d+)', self.src)
            if am:
                k4 = int(am.group(1))
        if k4 is None and len(nums) > 3:
            k4 = nums[3]
        if k4 is None:
            return None
        return (k1, k2, k3, k4)

    def blockseedadjust(self):
        m = re.search('0x45d9f3b', self.src)
        if not m:
            return 0
        ik = re.search('IK\\((\\d+),0\\)', self.src[m.start():m.start() + 900])
        if ik:
            irm = re.search('Ir\\[' + ik.group(1) + '\\]=(\\d+)', self.src)
            if irm:
                return int(irm.group(1))
        return 0

    def decryptstring(self, pool: bytes, offsets: list, key: int, tt: int, sid: int):
        if sid < 1 or sid > len(offsets):
            return None
        off = offsets[sid - 1]
        if off < 1 or off + 3 >= len(pool):
            return None
        ln = pool[off - 1] | pool[off] << 8 | pool[off + 1] << 16 | pool[off + 2] << 24
        if off + 4 + ln > len(pool):
            return None
        c1, c2 = self.strseedconsts()
        t = (key + sid * 257 + ln * 131 + c1 + c2 + (tt & 65535) * 17 + 21417) % u32
        t = (t * 1664525 + 1013904223 + sid * 40503 + ln * 11117 + (tt >> 16 & 65535) * 29) % u32
        if t == 0:
            t = (key + 1) % u32
        tb0, tb1, tb2, tb3 = (tt & 255, tt >> 8 & 255, tt >> 16 & 255, tt >> 24 & 255)
        out = bytearray()
        for k in range(1, ln + 1):
            t = (t * 1664525 + 1013904223 + sid * 257 + k * 131 + ln * 17 + (tt & 65535) * 3 + 1831565813) % u32
            ha = t & 255
            ha2 = t >> 8 & 255
            he = t >> 16 & 255
            hx = t >> 24 & 255
            mask = ha ^ ha2 + k + tb0 & 255 ^ (he ^ tb2 ^ hx + sid + ln + tb1 + tb3 & 255)
            out.append(pool[off + 3 + k - 1] ^ mask)
        return bytes(out)

    def parse(self):
        mega = self.findmega()
        if mega is None:
            return False
        name = mega.group(1)
        text = luaunescape(mega.group(2)).decode('latin-1')
        parts = sorted(((int(m.group(1)), int(m.group(2))) for m in re.finditer(re.escape(name) + ':sub\\((\\d+),(\\d+)\\)', self.src)))
        if len(parts) < 4:
            self.warnings.append('VM payload string present but not partitioned (truncated?)')
            return False
        ppool = text[parts[0][0] - 1:parts[0][1]]
        poff = text[parts[1][0] - 1:parts[1][1]]
        pmap = text[parts[2][0] - 1:parts[2][1]]
        pwpt = text[parts[3][0] - 1:parts[3][1]]
        tabs = self.tablealphabets()
        if not tabs:
            self.warnings.append('no base91 table alphabet found (truncated?)')
            return False
        envkey = self.extractenvchain()
        mixerp = self.mixerparams()
        if envkey is None or mixerp is None:
            self.warnings.append('could not recover the key-schedule constants')
            return False
        lz, la = mixerp

        def mixer(s):
            return ((lz ^ s * 40503 % i31) + la) % i31 * 48271 % i31
        skey = self.stringkey(envkey)
        if skey is None:
            self.warnings.append('could not recover the string-table key')
            return False
        key, tt = skey
        offs = varintdeltastream(b91decode(poff, tabs[0]))
        best = None
        for cand in (lz77decompress(b91decode(ppool, tabs[0]), 1 << 26), b91decode(ppool, tabs[0])):
            score = 0.0
            for sid in (1, 2, 3, 4, 5):
                s = self.decryptstring(cand, offs, key, tt, sid)
                if s:
                    score += printableratio(s)
            if best is None or score > best[0]:
                best = (score, cand)
        score, pool = best
        if score < 3.5:
            self.warnings.append(f'string-table key sanity score low ({score:.1f}/5)')
        self.inlinemap = varintstream(lz77decompress(b91decode(pmap, tabs[0]), 1 << 26))
        for sid in range(1, len(offs) + 1):
            s = self.decryptstring(pool, offs, key, tt, sid)
            if s is not None:
                self.strings[sid] = s.decode('latin-1')
        wk = self.wptkey(mixer, envkey)
        if wk is None:
            self.warnings.append('could not recover the WPT blob key')
            return False
        k1, wptkey = wk
        outlen = None
        if '==87 and' in self.src:
            om = re.search('\\(\\w+ or (\\d+)\\)\\)', self.src[self.src.find('==87 and'):self.src.find('==87 and') + 400])
            if om:
                outlen = int(om.group(1))
        wm = re.search(r'\*65536\)local \w+=\(\w+==(\d+)\)', self.src)
        wmagic = int(wm.group(1)) if wm else None

        def magicok(buf):
            if buf[:3] == b'WPT':
                return True
            if wmagic is not None and len(buf) >= 3:
                return buf[0] + buf[1] * 256 + buf[2] * 65536 == wmagic
            return False

        data = None
        for alpha in self.stringalphabets() + tabs:
            blob = b91decode(pwpt, alpha)
            dec = bytearray()
            kk = wptkey
            for b in blob:
                dec.append(b ^ kk & 255)
                kk = (kk * 48271 + 81) % i31
            if magicok(dec):
                data = bytes(dec)
                break
            try:
                d2 = lz77decompress(bytes(dec), outlen or 1 << 26)
            except Exception:
                continue
            if magicok(d2):
                data = d2
                break
        if data is None:
            self.warnings.append('could not decode the WPT bytecode blob')
            return False
        self.wptversion = data[3]
        if self.wptversion not in (51, 52):
            self.warnings.append(f'unsupported WPT version {self.wptversion - 48}; strings recovered, bytecode listing skipped')
            return True
        if self.wptversion == 52 and wmagic is not None \
                and data[4] == (envkey % 251) + 1 and varint(data, 4)[0] > 5000:
            if self.parsegen3(data, envkey):
                return True
            self.warnings.append('newer WPT4 proto layout (second-generation build); '
                                 'VM string table recovered, bytecode devirtualization '
                                 'of this build generation is not supported yet')
            return True
        bc = self.blockconstants()
        if not bc:
            self.warnings.append('could not recover block-key constants')
            return True
        self.k12, self.k22, self.k32, self.k42 = bc
        self.adjust = self.blockseedadjust()
        self.envkey = envkey
        self.mixer = mixer
        self.k1 = k1
        self.parseprototypes(data)

        self.extracthandlers()

        self.buildnamemaps()

        return True

    def parseprototypes(self, data: bytes):
        pos = 5 if self.wptversion == 51 else 4
        if self.wptversion == 52 and self.envkey is not None \
                and pos < len(data) and data[pos] == (self.envkey % 251) + 1:
            pos += 1
        n, pos = varint(data, pos)
        colids = []
        bw = re.search('=zn\\(n8\\[zk\\[\\d+\\]\\],zn\\(', self.src) or re.search('=O6\\(O9\\[IF\\[\\d+\\]\\],O6\\(', self.src)
        if bw:
            seg = self.src[bw.start():bw.start() + 4000]
            colids = [int(x) for x in re.findall('\\w+\\[(\\d+)\\]\\[\\w+\\]\\s*=\\s*\\w', seg)]
            seen, uniq = (set(), [])
            for c in colids:
                if c not in seen:
                    seen.add(c)
                    uniq.append(c)
            colids = uniq[:8]
        self.colids = colids
        self.ukb = extractukbias(self.src)
        self.uyur = extractuyur(self.src)
        self.je = extractje(self.src)
        self.junkops = extractjunkops(self.src)
        self.cond = extractcond(self.src)
        for pid in range(n):
            P = {'pid': pid}
            cnt, pos = varint(data, pos)
            P['n'] = cnt
            for _ in range(4):
                _, pos = varint(data, pos)
            nmk, pos = varint(data, pos)
            for _ in range(nmk):
                _, pos = varint(data, pos)
            P['numparams'] = data[pos]
            P['x4752'] = data[pos + 1]
            P['is_vararg'] = data[pos + 2]
            nup = data[pos + 3]
            pos += 4
            P['upvals'] = []
            for _ in range(nup):
                P['upvals'].append((data[pos] == 1, data[pos + 1]))
                pos += 2
            P['ops'] = list(data[pos:pos + cnt])
            pos += cnt
            if self.wptversion == 51:
                ufd = []
                for _ in range(cnt):
                    v, pos = varint(data, pos)
                    ufd.append(v)
                tf, pos = varint(data, pos)
                ufp = []
                for _ in range(2 * tf):
                    v, pos = varint(data, pos)
                    ufp.append(v)
                P['uf_deltas'], P['uf_pairs'] = (ufd, ufp)
            rawlen, pos = varint(data, pos)
            P['raw'] = data[pos:pos + rawlen]
            pos += rawlen
            nblk, pos = varint(data, pos)
            offs, total = ([], 0)
            for _ in range(nblk):
                v, pos = varint(data, pos)
                total += v
                offs.append(total)
            P['blk_off'] = offs
            P['blk_len'] = []
            for _ in range(nblk):
                v, pos = varint(data, pos)
                P['blk_len'].append(v)
            P['blk_flag'] = []
            for _ in range(nblk):
                P['blk_flag'].append(data[pos])
                pos += 1
            pos += 1
            njmp, pos = varint(data, pos)
            ukp = []
            for _ in range(2 * njmp):
                v, pos = varint(data, pos)
                ukp.append(v)
            P['uk_pairs'] = ukp
            P['regs'] = [dict() for _ in range(8)]
            P['key'] = self.mixer((self.k1 ^ pid) % i31) % i31 or 1
            self.protos.append(P)
        self.wptconsumed = pos
        self.wpttotal = len(data)
        for P in self.protos:
            self.decryptblocks(P)
            self.buildjumptables(P)
            self.builduf(P)

    def buildjumptables(self, P):
        pid = P['pid']
        P['uk'] = {}
        if self.ukb and len(P['uk_pairs']) >= 2:
            te = self.ukb['te'](pid)
            tx = self.ukb['tx'](pid)
            kp = self.ukb['keypos']
            it = iter(P['uk_pairs'])
            for a, b in zip(it, it):
                if kp == 1:
                    P['uk'][a - te] = b - tx
                else:
                    P['uk'][b - te] = a - tx
        P['ue'] = {}
        if self.cond and self.uyur:
            lit = self.cond['lit'].get(pid)
            if lit:
                uy = self.uyur['uy'](pid)
                ur = self.uyur['ur'](pid)
                ja = self.cond['ja'](pid)
                jc = self.cond['jc'](pid)
                tab = {}
                for i in range(0, len(lit) - 1, 2):
                    a, b = (lit[i], lit[i + 1])
                    if self.cond['order'] == 'key_first':
                        tab[a - ja] = b - jc
                    else:
                        tab[b - ja] = a - jc
                P['ue'] = {k - uy: v - ur for k, v in tab.items()}

    def builduf(self, P):
        if self.wptversion == 51:
            uf = {}
            c = 0
            for i, d in enumerate(P.get('uf_deltas', [])[:P['n']]):
                c += d
                uf[i + 1] = c
            ufx = {}
            a = b = 0
            it = iter(P.get('uf_pairs', []))
            for x, y in zip(it, it):
                a += x
                b += y
                ufx[a] = b
            P['uf'], P['ufx'] = (uf, ufx)
        else:
            uf, ufx = ({}, {})
            pg = 0
            for i in range(1, P['n'] + 1):
                uf[i] = pg
                ufx[pg] = i
                pg += (self.je or {}).get(P['ops'][i - 1], 4)
            P['uf'], P['ufx'] = (uf, ufx)

    def decryptblocks(self, P):
        envkey = self.envkey

        def fnv(*vals):
            h = 2166136261
            for v in vals:
                h = (h ^ v) * 16777619 % u32
            return h
        nblk = (P['n'] + 63) // 64
        for blk in range(nblk):
            lo = blk * 64 + 1
            hi = min(lo + 63, P['n'])
            if lo > hi:
                break
            xt = (self.k22 ^ self.k32 ^ (P['pid'] * 73244475 % u32 ^ envkey * 668265261 % u32)) % i31
            xj = self.mixer(xt) % i31 or 1
            xf = (P['pid'] * 2654435769 + blk * 2246822507 + P['key'] + xj) % i31
            hk = self.mixer((self.k12 ^ xf) % i31) % i31
            hk = (hk + self.adjust) % i31
            if hk == 0:
                hk = 1
            if hk % 256 == 0:
                hk += 1
            so = P['blk_off'][blk] if blk < len(P['blk_off']) else 0
            deflen = (hi - lo + 1) * 8
            hlen = P['blk_len'][blk] if blk < len(P['blk_len']) else deflen
            flag = P['blk_flag'][blk] if blk < len(P['blk_flag']) else 0
            ha = (P['pid'] + 1) * 2146121005 % u32
            hn = (blk + 1) * 2221713035 % u32
            hv = so % 65536 * 2654435761 % u32
            hl = hlen % 65536 * 2246822519 % u32
            hq = (lo * 131 + hi * 17 + flag) % 256 * 3266489917 % u32
            hx = self.mixer((self.k42 ^ ha ^ hn ^ hv ^ hl ^ hq ^ envkey) % i31) % i31 or 1
            hk = (hk ^ hx) % i31
            if hk % 256 == 0:
                hk += 1
            raw = P['raw']
            buf = bytearray()
            k = hk
            for i in range(hlen):
                b = raw[so + i] if so + i < len(raw) else 0
                buf.append(b ^ k & 255)
                k = (k * 48271 + 81) % i31
            if flag % 2:
                buf = lz77decompress(bytes(buf), deflen)
            nz = hi - lo + 1
            for v in range(lo, hi + 1):
                if flag >= 2:
                    o = v - lo
                    vals = [buf[o + nz * c] if o + nz * c < len(buf) else 0 for c in range(8)]
                else:
                    o = (v - lo) * 8
                    vals = [buf[o + c] if o + c < len(buf) else 0 for c in range(8)]
                for c in range(8):
                    P['regs'][c][v] = vals[c]
                if v == lo:
                    first = vals
            if P['pid'] == 0 and blk == 0:
                u = (first[0] * 65599 + first[1] * 31 + first[2]) % i31 or 1
                uv = u ^ self.k22 ^ self.k32 * 31 % i31
                uv = (uv + self.k42) % i31
                if self.variant == 'B':
                    d0 = (envkey ^ 257 ^ self.k22 ^ self.k42) % i31 or 1
                    d6 = (d0 * 48271 + 81) % i31 or 1
                    uv = (uv + d6) % i31 or 1
                P['key'] = (uv * 48271 + 81) % i31 or 1
            else:
                xk = fnv(*first)
                xc = blk * 2654435769
                xw = xc % u32
                xo = (xc - xw) // u32
                xv = xw ^ P['key'] ^ xk
                xe = (xo * u32 + xv) % i31
                P['key'] = (xe * 48271 % u32 + 81) % i31 or 1

    def parsegen3(self, data, envkey):
        try:
            protos, consumed = gen3.parsev52(data, envkey)
        except Exception:
            return False
        if not protos or abs(consumed - len(data)) > 64:
            return False
        nchk = sum(1 for p in protos if p.key7194 != 0)
        if nchk < len(protos) * 0.9:
            return False
        self.g3 = True
        for p in protos:
            gen3.drive(p)
            P = {'pid': p.pid, 'n': p.n, 'numparams': p.numparams,
                 'is_vararg': 1 if p.vararg else 0, 'upvals': list(p.upvals),
                 'ops': p.ops,
                 'regs': [p.cols[c] for c in (8727, 5102, 8959, 1228, 1514, 6151, 6134)] + [{}],
                 'uk': dict(p.jumps), 'x7059': dict(p.x7059), 'g3': p}
            self.protos.append(P)
        self.wptconsumed = consumed
        self.wpttotal = len(data)
        self.extracthandlersg3()
        return True

    def extracthandlersg3(self):
        best = (0, None)
        for m in re.finditer(r'local (\w+)=\(?(Ih\[\d+\]|\w+)\)?\[tH\]', self.src):
            opvar = m.group(1)
            cnt = len(re.findall('if\\s+' + opvar + '==(\\d+)\\s+then\\b', self.src))
            if cnt > best[0]:
                best = (cnt, opvar)
        if best[0] < 10:
            return
        opvar = best[1]
        pat = re.compile('if\\s+' + opvar + r'==(\d+)\s+then\s+')
        tok = re.compile('(?:\'[^\']*\'|"[^"]*")|\\b(do|if|function|repeat|elseif|else|end|until)\\b')
        for m in pat.finditer(self.src):
            op = int(m.group(1))
            pos = m.end()
            depth = 0
            start = pos
            for tm in tok.finditer(self.src, pos):
                t = tm.group(1)
                if not t:
                    continue
                if t in ('do', 'if', 'function', 'repeat'):
                    depth += 1
                elif t in ('end', 'until'):
                    if depth == 0:
                        body = self.src[start:tm.start()]
                        if 'tH' in body or 'tP' in body or 'tu=true' in body or 'tv=true' in body:
                            self.handlers[op] = body.strip()
                        break
                    depth -= 1

    def extracthandlers(self):
        for key in ('n8[zk[36934]]=function', 'O9[IF[18603]]=function'):
            idx = self.src.find(key)
            if idx >= 0:
                break
        else:
            idx = 0
        vm = self.src[idx:]
        opvar = 'Ml' if 'n8[zk[36934]]=function' in self.src[:idx + 40] or self.src.find('n8[zk[36934]]=function') == idx else 'Q1'
        if self.src.find('O9[IF[18603]]=function') == idx:
            opvar = 'Q1'
        pat = re.compile(f'do\\s+local\\s+(\\w+)\\s*=\\s*{opvar}-(\\d+);if\\s+([^t]+)\\s+then\\s+')
        tok = re.compile('(?:\'[^\']*\'|\\"[^\\"]*\\")|\\b(do|if|function|repeat|elseif|else|end|until)\\b')
        for m in pat.finditer(vm):
            var, base, cond = (m.group(1), int(m.group(2)), m.group(3))
            diffs = [0] + [int(x) for x in re.findall(f'{var}-(\\d+)', cond)]
            pos = m.end()
            mif = re.match(f'\\s*if\\s+{opvar}[<>]=?(\\d+)\\s+then\\b', vm[pos:])
            if not mif:
                continue
            pos += mif.end()
            depth = 0
            start = pos
            branches = []
            for tm in tok.finditer(vm, pos):
                t = tm.group(1)
                if not t:
                    continue
                if t in ('do', 'if', 'function', 'repeat'):
                    depth += 1
                elif t in ('end', 'until'):
                    if depth == 0:
                        branches.append(vm[start:tm.start()])
                        break
                    depth -= 1
                elif depth == 0 and t in ('elseif', 'else'):
                    branches.append(vm[start:tm.start()])
                    if t == 'elseif':
                        mei = re.match(f'\\s*{opvar}[<>]=?(\\d+)\\s+then\\b', vm[tm.end():])
                        if mei:
                            start = tm.end() + mei.end()
                    else:
                        start = tm.end()
            for off, body in zip(diffs, branches):
                self.handlers[base + off] = body.strip()

    def buildnamemaps(self):
        if not self.colids or not self.protos:
            return
        id2col = {tid: c for c, tid in enumerate(self.colids)}
        self.id2col = id2col
        for key in ('n8[zk[36934]]=function', 'O9[IF[18603]]=function'):
            idx = self.src.find(key)
            if idx >= 0:
                break
        else:
            idx = 0
        vm = self.src[idx:idx + 8000]
        cont = 'XH' if 'XH[' in vm[:2000] else 'Jq'
        self.container = cont
        names = {}
        for m in re.finditer('(\\w+)=' + cont + '\\[(\\d+)\\]', vm):
            if m.group(1) != cont and int(m.group(2)) in id2col:
                names[m.group(1)] = id2col[int(m.group(2))]
        for _ in range(5):
            changed = False
            for m in re.finditer('(\\w+)=(\\w+)[,;\\s)&|]', vm):
                if m.group(1) != cont and m.group(2) in names and (m.group(1) not in names):
                    names[m.group(1)] = names[m.group(2)]
                    changed = True
            if not changed:
                break
        self.colnames = names

    def colof(self, token):
        m = re.fullmatch('(\\w+)\\[(\\d+)\\]', token)
        if m and m.group(1) == getattr(self, 'container', ''):
            return self.id2col.get(int(m.group(2)))
        return self.colnames.get(token)

    def resolveinline(self, P, i):
        op = P['ops'][i - 1]
        body = self.handlers.get(op)
        if not body:
            return []
        masks = [(int(a), int(b)) for a, b in re.findall('\\(\\((?:Mt|Qp)\\*(\\d+)\\)\\+(\\d+)\\)', body)]
        if self.variant == 'A':
            zns = re.findall('zn\\(\\(?([\\w\\[\\]]+)\\[Mt\\]', body)
        else:
            zns = re.findall('O6\\(\\(?([\\w\\[\\]]+)\\[Qp\\]', body)
        if not masks or not zns:
            return []
        out = []
        pair = 0
        for j in range(0, len(zns), 2):
            if j + 1 >= len(zns):
                break
            locol = self.colof(zns[j])
            hicol = self.colof(zns[j + 1])
            if locol is None or hicol is None:
                continue
            m1 = masks[2 * pair % len(masks)]
            m2 = masks[(2 * pair + 1) % len(masks)]
            mask1 = (i * m1[0] + m1[1]) % 256
            mask2 = (i * m2[0] + m2[1]) % 256
            uc = (P['regs'][locol][i] ^ mask1) + (P['regs'][hicol][i] ^ mask2) * 256
            if 0 <= uc < len(self.inlinemap):
                sid = self.inlinemap[uc]
                if sid != 65535:
                    s = self.strings.get(sid)
                    if s is not None:
                        out.append(s)
            pair += 1
        return out

    def instructionlines(self):
        lines = []
        for P in sorted(self.protos, key=lambda p: p['pid']):
            lines.append(f"-- prototype {P['pid']}  ({P['n']} instructions)")
            for i in range(1, P['n'] + 1):
                op = P['ops'][i - 1]
                regs = [P['regs'][c].get(i, 0) for c in range(8)]
                if P.get('g3') is not None:
                    inl = []
                else:
                    inl = self.resolveinline(P, i)
                tag = '  ; ' + ', '.join((ascii(s) for s in inl)) if inl else ''
                jmp = f"  -> {P['uk'][i]}" if P.get('g3') is not None and i in P['uk'] else ''
                lines.append(f'  [{i:4d}] op={op:3d}  A={regs[0]:3d} B={regs[1]:3d} C={regs[2]:3d} D={regs[3]:3d} E={regs[4]:3d} F={regs[5]:3d} G={regs[6]:3d} H={regs[7]:3d}{jmp}{tag}')
        return lines
