from __future__ import annotations
import re
from .util import b91decode, i31, lz77decompress
from .luaparse import fold, parselua
from .decode import buildspec, constspecs, sbxpairs

class sym2:
    __slots__ = ('k', 'a', 'b', 'c', 'd')

    def __init__(self, k, a=None, b=None, c=None, d=None):
        self.k, self.a, self.b, self.c, self.d = (k, a, b, c, d)

    def __repr__(self):
        if self.k == 'col':
            return f'C{self.a}'
        if self.k == 'xcol':
            return f'(C{self.a}^{self.b},{self.c},{self.d})'
        if self.k == 'reg':
            return f'R[{self.a!r}]'
        if self.k == 'inl':
            return f'INL{self.a}({self.b!r})'
        if self.k == 'pool':
            return f'POOL({self.a!r})'
        if self.k == 'lit':
            return repr(self.a)
        if self.k == 'env':
            return f'ENV[{self.a!r}]'
        if self.k == 'bin':
            return f'({self.a!r}{self.b}{self.c!r})'
        if self.k == 'un':
            return f'{self.a}({self.b!r})'
        if self.k == 'call':
            return f'{self.a!r}({self.b!r})'
        if self.k == 'pc':
            return 'PC'
        if self.k == 'top':
            return 'TOP'
        if self.k == 'sbx':
            return f'SBX({self.a!r},{self.b!r})'
        if self.k == 'upv':
            return f'UPV[{self.a!r}]'
        if self.k == 'cells':
            return f'CELLS[{self.a!r}]'
        if self.k == 'uk':
            return 'UK[PC]'
        if self.k == 'uekey':
            return 'UE[PC+UY]'
        if self.k == 'uf':
            return 'UF[PC]'
        if self.k == 'opaque':
            return f'?{self.a}'
        return f'<{self.k}:{self.a}:{self.b}:{self.c}:{self.d}>'

def L(v):
    return sym2('lit', v)

class normstate:

    def __init__(self, sem):
        self.sem = sem
        self.env = {}
        self.writes = []
        self.topsets = []
        self.upvwrites = []
        self.cellwrites = []
        self.calls = []
        self.jumps = []
        self.returns = []
        self.constuses = []
        self.depth = 0

    def sub(self, cond):
        n = normstate(self.sem)
        n.env = dict(self.env)
        n.writes = list(self.writes)
        n.topsets = list(self.topsets)
        n.upvwrites = list(self.upvwrites)
        n.cellwrites = list(self.cellwrites)
        n.calls = list(self.calls)
        n.jumps = list(self.jumps)
        n.returns = list(self.returns)
        n.constuses = list(self.constuses)
        n.depth = self.depth
        n.cond = cond
        return n

class normalizer:
    maxstmt = 400

    def __init__(self, sem):
        self.sem = sem

    def run(self, ast):
        self.st = normstate(self.sem)
        self.st.cond = sym2('lit', True)
        self.nstmt = 0
        try:
            self.execblock(ast)
        except RecursionError:
            pass
        return self.st

    def execblock(self, stmts):
        for st in stmts:
            self.nstmt += 1
            if self.nstmt > self.maxstmt:
                return
            self.execstmt(st)

    def execstmt(self, st):
        k = st[0]
        if k == 'local':
            names, exprs = (st[1], st[2])
            vals = [self.ev(e) for e in exprs]
            for i, nm in enumerate(names):
                self.st.env[nm] = vals[i] if i < len(vals) else sym2('nilv')
        elif k == 'assign':
            target, val = (st[1], self.ev(st[2]))
            self.assign(target, val)
        elif k == 'massign':
            targets, exprs = (st[1], st[2])
            vals = [self.ev(e) for e in exprs]
            for i, t in enumerate(targets):
                if i < len(vals):
                    self.assign(t, vals[i])
        elif k == 'if':
            cond, then, elifs, els = (st[1], st[2], st[3], st[4])
            branches = [('and', cond, then)] + [('and', c, b) for c, b in elifs]
            if els:
                branches.append(('else', None, els))
            self.execbranches(branches)
        elif k == 'callstat':
            e = self.evcall(st[1])
            if e is not None and e.k == 'call':
                self.st.calls.append((e.a, e.b, None, self.st.cond))
        elif k == 'return':
            vals = [self.ev(e) for e in st[1]]
            if not vals:
                self.st.returns.append(('bare', None, self.st.cond))
            elif len(vals) == 1:
                self.st.returns.append(('val', vals[0], self.st.cond))
            else:
                self.st.returns.append(('multi', vals, self.st.cond))
        elif k in ('do',):
            self.execblock(st[1])
        elif k == 'while':
            pass
        elif k in ('fornum', 'forin'):
            pass
        elif k == 'repeat':
            pass
        elif k == 'break':
            pass

    def execbranches(self, branches):
        for kind, cond, body in branches:
            sub = normstate(self.sem)
            sub.env = dict(self.st.env)
            sub.cond = self.st.cond
            old = self.st
            self.st = sub
            self.nstmt += 1
            self.execblock(body)
            self.st = old
            for w in sub.writes:
                old.writes.append(w)
            for w in sub.topsets:
                old.topsets.append(w)
            for w in sub.upvwrites:
                old.upvwrites.append(w)
            for w in sub.cellwrites:
                old.cellwrites.append(w)
            for w in sub.calls:
                old.calls.append(w)
            for w in sub.jumps:
                old.jumps.append(w)
            for w in sub.returns:
                old.returns.append(w)
            for w in sub.constuses:
                old.constuses.append(w)
            old.env.update({k: v for k, v in sub.env.items()})

    def assign(self, target, val):
        if target[0] == 'index':
            base, idx = (target[1], target[2])
            bs = base[1] if base[0] == 'var' else None
            if bs == 'R':
                idxs = self.ev(idx)
                self.st.writes.append((idxs, val, self.st.cond))
                return
            if bs == 'TOP':
                self.st.topsets.append((val, self.st.cond))
                return
            if bs == 'PC':
                self.assignpc(idx, val)
                return
            if bs == 'UPV':
                self.st.upvwrites.append((self.ev(idx), val, self.st.cond))
                return
            if bs == 'CELLS':
                self.st.cellwrites.append((self.ev(idx), val, self.st.cond))
                return
            m = re.match('^@(\\d)$', bs or '')
            if m:
                self.st.env[f'__col{m.group(1)}'] = val
                return
            if base[0] == 'index':
                b2 = base[1]
                if b2[0] == 'var' and b2[1] == 'R':
                    dest = self.ev(base[2])
                    key = self.ev(idx)
                    self.st.writes.append((dest, sym2('settable', key, val), self.st.cond))
                    return
            return
        if target[0] == 'var':
            self.st.env[target[1]] = val
            return

    def assignpc(self, idx, val):
        if idx[0] == 'var' and idx[1] == 'PC':
            pass
        vs = self.ev(val) if val is not None else None
        self.st.jumps.append(('expr', vs, self.st.cond))

    def ev(self, e):
        if e is None:
            return sym2('nilv')
        k = e[0]
        if k == 'num':
            return L(e[1])
        if k == 'str':
            return L(e[1])
        if k == 'bool':
            return L(e[1])
        if k == 'nilv':
            return sym2('nilv')
        if k == 'var':
            nm = e[1]
            if nm in self.st.env:
                return self.st.env[nm]
            if nm == 'PC':
                return sym2('pc')
            if nm == 'TOP':
                return sym2('top')
            if nm == 'ENV':
                return sym2('envtable')
            if nm == 'MAP':
                return sym2('maptable')
            if nm == 'POOL':
                return sym2('pooltable')
            if nm == 'PROTOS':
                return sym2('protostable')
            if nm == 'UPV':
                return sym2('upvtable')
            if nm == 'CELLS':
                return sym2('cellstable')
            if nm == 'UK':
                return sym2('uktable')
            if nm == 'UE':
                return sym2('uetable')
            if nm == 'UF':
                return sym2('uftable')
            if nm == 'UFX':
                return sym2('ufxtable')
            if nm == 'R':
                return sym2('rtable')
            return sym2('opaque', nm)
        if k == 'un':
            return sym2('un', e[1], self.ev(e[2]))
        if k == 'bin':
            op = e[1]
            l = self.ev(e[2])
            r = self.ev(e[3])
            if l.k == 'lit' and r.k == 'lit' and isinstance(l.a, (int, float)) and isinstance(r.a, (int, float)):
                try:
                    if op == '+':
                        return L(l.a + r.a)
                    if op == '-':
                        return L(l.a - r.a)
                    if op == '*':
                        return L(l.a * r.a)
                    if op == '/':
                        return L(l.a / r.a) if r.a else sym2('bin', op, l, r)
                    if op == '%':
                        return L(l.a % r.a) if r.a else sym2('bin', op, l, r)
                    if op == '^':
                        return L(l.a ** r.a)
                except Exception:
                    pass
            return sym2('bin', op, l, r)
        if k == 'index':
            return self.evindex(e)
        if k == 'call':
            c = self.evcall(e)
            return c if c is not None else sym2('opaque', 'call')
        if k == 'function':
            return sym2('opaque', 'function')
        if k == 'table':
            return sym2('opaque', 'table')
        if k == 'vararg':
            return sym2('vararg')
        return sym2('opaque', k)

    def evindex(self, e):
        base, idx = (e[1], e[2])
        if base[0] == 'var':
            nm = base[1]
            m = re.match('^@(\\d)$', nm)
            if m:
                if idx[0] == 'var' and idx[1] == 'PC':
                    col = int(m.group(1))
                    return sym2('col', col)
                return sym2('opaque', f'col{nm}')
            if nm == 'R':
                return sym2('reg', self.ev(idx))
            if nm == 'ENV':
                return sym2('env', self.ev(idx))
            if nm == 'POOL':
                return sym2('pool', self.ev(idx))
            if nm == 'PROTOS':
                return sym2('proto', self.ev(idx))
            if nm == 'UPV':
                return sym2('upv', self.ev(idx))
            if nm == 'MAP':
                return sym2('mapidx', self.ev(idx))
            if nm == 'UK':
                if idx[0] == 'var' and idx[1] == 'PC':
                    return sym2('uk')
                return sym2('opaque', 'uk')
            if nm == 'UE':
                return sym2('ueval', self.ev(idx))
            if nm == 'UF':
                if idx[0] == 'var' and idx[1] == 'PC':
                    return sym2('uf')
                return sym2('opaque', 'uf')
            if nm == 'TOP':
                return sym2('top')
            return sym2('opaque', nm)
        if base[0] == 'index':
            inner = self.evindex(base)
            key = self.ev(idx)
            if inner.k == 'reg':
                return sym2('gettable', inner.a, key)
            if inner.k == 'env':
                return sym2('envget', inner.a, key)
            if inner.k == 'upv':
                return sym2('upvgettable', inner.a, key)
            if inner.k == 'mapidx':
                return sym2('opaque', 'map2')
            if inner.k == 'opaque' and inner.a == 'envtable':
                return sym2('env', key)
            return sym2('index2', inner, key)
        return sym2('opaque', 'index')

    def evcall(self, e):
        fn, args = (e[1], e[2])
        argv = [self.ev(a) for a in args]
        fnsym = self.ev(fn) if fn[0] != 'var' or fn[1] != self.sem.V.get('dec') else sym2('decfn')
        if fn[0] == 'bin' and fn[1] == 'or':
            lft = fn[2]
            if lft[0] == 'bin' and lft[1] == 'and':
                core = lft[2]
                fnsym = self.ev(core)
        elif fn[0] == 'var' and fn[1] == self.sem.V.get('dec'):
            fnsym = sym2('decfn')
        else:
            fnsym = self.ev(fn)
        if fnsym.k == 'decfn' and argv:
            a0 = argv[0]
            if a0.k == 'mapidx':
                return sym2('inl', self.sem.nextconstordinal(), a0.a)
            return sym2('dec', a0)
        if fnsym.k in ('reg', 'env', 'upv', 'lit', 'gettable', 'envget', 'upvgettable', 'opaque', 'proto'):
            return sym2('call', fnsym, argv)
        return sym2('call', fnsym, argv)
loadlibtable = {40: 'type', 12: 'math.floor', 7: 'math.ceil', 2: 'math.abs', 25: 'math.sqrt', 21: 'math.pow', 24: 'math.sin', 9: 'math.cos', 27: 'math.tan', 11: 'math.exp', 10: 'math.deg', 17: 'math.log', 22: 'math.rad', 19: 'math.min', 18: 'math.max', 45: 'table.insert', 46: 'unpack', 42: 'string.byte', 43: 'string.char', 44: 'string.len', 41: 'typeof', 57: 'select', 60: 'rawset', 61: 'rawget', 62: 'rawequal', 64: 'rawlen', 3: 'math.asin', 4: 'math.acos', 5: 'math.atan2', 6: 'math.atan', 13: 'math.fmod', 14: 'math.ldexp', 20: 'math.modf'}

def extractukbias(src):
    f1 = re.search('local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+(\\w+)\\*211\\)%8209\\)', src)
    f2 = re.search('local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+(\\w+)\\*397\\)%12301\\)', src)
    f3 = re.search('local (\\w+)=(\\d+)\\+\\(\\(\\((\\d+)\\)\\+\\((\\w+)\\*149\\)\\+37\\)%1009\\)', src)
    f4 = re.search('local (\\w+)=(\\d+)\\+\\(\\(\\(\\((\\d+)-\\(\\d+%1009\\)\\)/1009\\)\\+\\((\\w+)\\*269\\)\\+83\\)%1013\\)', src)
    if not (f1 and f2 and f3 and f4):
        return None
    tef = (int(f1.group(2)), int(f1.group(3)), int(f3.group(2)), int(f3.group(3)))
    txf = (int(f2.group(2)), int(f2.group(3)), int(f4.group(2)), int(f4.group(3)))

    def te(pid):
        a, s, b, c = tef
        return a + (s + pid * 211) % 8209 + (b + (c + pid * 149 + 37) % 1009)

    def tx(pid):
        a, s, b, c = txf
        return a + (s + pid * 397) % 12301 + (b + ((c - c % 1009) // 1009 + pid * 269 + 83) % 1013)
    lp = re.search('local (\\w+),(\\w+) \\1,\\w+=\\w+\\(\\w+,\\w+\\)\\2,\\w+=\\w+\\(\\w+,\\w+\\)local (\\w+),(\\w+) \\3=(\\w+)-(\\w+)[;\\s]*\\4=(\\w+)-(\\w+)[;\\s]*\\w+\\[\\3\\]=\\4', src)
    if not lp:
        return None
    keypos = 1 if lp.group(5) == lp.group(1) else 2
    return {'te': te, 'tx': tx, 'keypos': keypos}

def extractuyur(src):
    muy = re.search('(\\w+)=(\\d+)\\+\\(\\(\\((\\d+)\\)\\+\\(\\(\\((\\w+\\[\\d+\\])\\)or 0\\)\\*(\\d+)\\)\\+(\\d+)\\)%997\\)', src)
    mur = re.search('(\\w+)=(\\d+)\\+\\(\\(\\(\\((\\d+)-\\(\\d+%997\\)\\)/997\\)\\+\\(\\(\\((\\w+\\[\\d+\\])\\)or 0\\)\\*(\\d+)\\)\\+(\\d+)\\)%991\\)', src)
    if not (muy and mur):
        return None
    big = int(muy.group(3))
    m1 = int(muy.group(5))
    a1 = int(muy.group(6))
    b2 = int(mur.group(2))
    big2 = int(mur.group(3))
    m2 = int(mur.group(5))
    a2 = int(mur.group(6))
    return {'uy': lambda pid: int(muy.group(2)) + (big + pid * m1 + a1) % 997, 'ur': lambda pid: b2 + ((big2 - big2 % 997) // 997 + pid * m2 + a2) % 991}

def extractliteraltable(src, name):
    for m in re.finditer(re.escape(name) + '=\\{', src):
        start = m.end() - 1
        depth = 0
        for i in range(start, min(start + 300000, len(src))):
            if src[i] == '{':
                depth += 1
            elif src[i] == '}':
                depth -= 1
                if depth == 0:
                    body = src[start + 1:i]
                    if '[0]=' in body[:60]:
                        tbl = {}
                        for pm in re.finditer('\\[(\\d+)\\]=\\{([\\d,]*)\\}', body):
                            tbl[int(pm.group(1))] = [int(x) for x in pm.group(2).split(',') if x]
                        return tbl
                    break
    return None

def extractcond(src):
    m = re.search('local (\\w+)=\\{\\}do for (\\w+)=0,(\\d+) do local (\\w+)=(\\w+)\\[\\2\\]local (\\w+)=\\{\\}if \\4 then local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+\\2\\*193\\)%8191\\)local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+\\2\\*389\\)%12289\\)for (\\w+)=1,#\\4,2 do \\6\\[\\4\\[\\13\\]-\\7\\]=\\4\\[\\13\\+1\\]-\\10 end end \\1\\[\\2\\]=\\6 end end', src)
    order = 'key_first'
    if not m:
        m = re.search('local (\\w+)=\\{\\}do for (\\w+)=0,(\\d+) do local (\\w+)=(\\w+)\\[\\2\\]local (\\w+)=\\{\\}if \\4 then local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+\\2\\*193\\)%8191\\)local (\\w+)=(\\d+)\\+\\(\\((\\d+)\\+\\2\\*389\\)%12289\\)for (\\w+)=1,#\\4,2 do \\6\\[\\4\\[\\13\\+1\\]-\\7\\]=\\4\\[\\13\\]-\\10 end end \\1\\[\\2\\]=\\6 end end', src)
        order = 'key_second'
    if not m:
        return None
    lit = extractliteraltable(src, m.group(5))
    if lit is None:
        return None
    jabase, jasalt = (int(m.group(8)), int(m.group(9)))
    jcbase, jcsalt = (int(m.group(11)), int(m.group(12)))
    return {'lit': lit, 'order': order, 'np': int(m.group(3)), 'ja': lambda pid: jabase + (jasalt + pid * 193) % 8191, 'jc': lambda pid: jcbase + (jcsalt + pid * 389) % 12289}

def extractje(src):
    m = re.search('JE=\\{([^}]+)\\}', src)
    return {int(k): int(v) for k, v in re.findall('\\[(\\d+)\\]=(\\d+)', m.group(1))} if m else None

def extractjunkops(src):
    m = re.search('local (\\w+)=(\\d+) local (\\w+)=(\\d+) local (\\w+)=(\\w+)\\+1 while \\w+\\[\\w+\\]==\\w+ or \\w+\\[\\w+\\]==\\w+ do', src)
    return (int(m.group(2)), int(m.group(4))) if m else None

class semantics:

    def __init__(self, vm):
        self.vm = vm
        self.src = vm.src
        self.ok = True
        self.problems = []
        self.constordinal = 0
        self.vocab()
        self.loaderconsts()
        self.doubles2()
        self.keylists2()
        self.classify()
        for P in vm.protos:
            self.buildtables(P)

    def nextconstordinal(self):
        self.constordinal += 1
        return self.constordinal

    def vocab(self):
        vm, src = (self.vm, self.src)
        V = {}
        m = re.search("type\\((\\w+)\\)=='function'and \\1\\)or [\\w\\[\\]]+\\)\\((\\w+)\\[[^\\]]+\\],(\\w+)\\)", src)
        V['dec'], V['map'], V['key'] = (m.group(1), m.group(2), m.group(3))
        anchor = src.find('n8[zk[36934]]=function') if vm.container == 'Jq' else src.find('O9[IF[18603]]=function')
        vmregion = src[anchor:] if anchor >= 0 else src
        cand = {}
        for mm in re.finditer('(\\w+)\\[(\\w+)\\[(\\d+)\\]\\]=\\1\\[\\2\\[(\\d+)\\]\\]\\(\\{\\}', src):
            ref = f'{mm.group(1)}[{mm.group(2)}[{mm.group(3)}]]'
            cand[ref] = len(re.findall(re.escape(ref) + '\\[', vmregion))
        V['envref'] = max(cand, key=cand.get) if cand else None
        m = re.search('local (\\w+)=\\{\\}\\1\\[\\(?\\d+-\\d+\\)?\\]=\\1', src)
        V['regs'] = m.group(1)
        m = re.search('local (\\w+)=1 local \\w+=false local \\w+=0', src)
        V['pc'] = m.group(1)
        m = re.search('local (\\w+)=0 local (\\w+)=\\(\\((\\w+%2\\)~=0 and\\{\\}or nil)', src)
        V['top'] = m.group(1)
        m = re.search('local (\\w+)=\\(\\((\\w+%16\\)>=8 and\\{\\}or nil)', src)
        V['cells'] = m.group(1)
        fa = 'n8[zk[36934]]=function' if vm.container == 'Jq' else 'O9[IF[18603]]=function'
        m = re.search(re.escape(fa) + '\\((\\w+),(\\w+)\\)', src)
        V['upv'] = m.group(2)
        V['protos'] = None
        for m in re.finditer('(\\w+)=(\\w+)\\[\\w+\\]\\+\\(\\w+\\[\\w+\\]\\*256\\)', src):
            tmp = m.group(1)
            for m2 in re.finditer('=(\\w+)\\[' + re.escape(tmp) + '\\]if not', src):
                if m2.group(1) != V['regs']:
                    V['protos'] = m2.group(1)
                    break
            if V['protos']:
                break
        V['pool'] = None
        libref = 'n8[zk[' if 'n8[zk[' in src[:200000] else 'O9[IF[' if 'O9[IF[' in src else None
        V['libref'] = libref
        if libref:
            mp = re.search('local (\\w+)=' + re.escape(libref) + '\\d+\\]\\]\\(' + re.escape(libref) + '\\d+\\]\\],\\w+\\)', src)
            if mp:
                V['pool'] = mp.group(1)
        m = re.search('(\\w+)=' + re.escape(vm.container) + '\\[\\d+\\](\\w+)=(\\d+)\\+\\(\\(\\((\\d+)\\)\\+\\(\\(\\((\\w+)\\[\\d+\\]\\)or 0\\)\\*\\d+\\)\\+\\d+\\)%997\\)(\\w+)=(\\d+)\\+\\(\\(\\(\\((\\d+)-\\(\\d+%997\\)\\)/997\\)\\+\\(\\(\\((\\w+)\\[\\d+\\]\\)or 0\\)\\*\\d+\\)\\+\\d+\\)%991\\)(\\w+)=' + re.escape(vm.container) + '\\[\\d+\\]', src)
        V['ue'], V['uy'], V['ur'], V['uk'] = (m.group(1), m.group(2), m.group(6), m.group(10))
        m = re.search('(\\w+)=' + re.escape(vm.container) + '\\[(\\d+)\\](\\w+)=' + re.escape(vm.container) + '\\[(\\d+)\\]end end', src)
        V['uf'], V['ufx'] = (m.group(1), m.group(3))
        m = re.search('while (\\w+)\\[\\w+\\]==\\w+ or \\w+\\[\\w+\\]==\\w+ do', src)
        V['opsarr'] = m.group(1)
        m = re.search('=([\\w]+)\\(' + re.escape(vm.container) + '\\[\\w+\\[\\d+\\]\\],' if vm.container == 'Jq' else '', src)
        if vm.container == 'Jq':
            mx = re.search('=(\\w+)\\(n8\\[zk\\[\\d+\\]\\],\\1\\(', src)
        else:
            mx = re.search('=(\\w+)\\(O9\\[IF\\[\\d+\\]\\],\\1\\(', src)
        V['xor'] = mx.group(1) if mx else None
        V['cols'] = {}
        for name, col in vm.colnames.items():
            V['cols'].setdefault(col, set()).add(name)
        V['colid2col'] = {tid: c for c, tid in enumerate(vm.colids)}
        for tid, col in V['colid2col'].items():
            V['cols'].setdefault(col, set()).add(f'{vm.container}[{tid}]')
        self.V = V

    def loaderconsts(self):
        self.ukb = extractukbias(self.src)
        self.uyur = extractuyur(self.src)
        self.cond = extractcond(self.src)
        self.je = extractje(self.src)
        self.junkops = extractjunkops(self.src)
        if not self.ukb:
            self.problems.append('UK bias formulas not found')
            self.ok = False
        if not self.uyur:
            self.problems.append('Uy/UR formulas not found')
            self.ok = False
        if not self.cond:
            self.problems.append('cond-jump table not found')
            self.ok = False

    def doubles2(self):
        src = self.src
        self.doubles = {}
        lib = self.V.get('libref') or ('n8[zk[' if 'n8[zk[' in src else 'O9[IF[')
        m = re.search(re.escape(lib) + '(\\d+)\\]\\]=(\\d+) local (\\w+)=\\(function\\(\\)local \\w+=\\{\\}for \\w+=1,' + re.escape(lib) + '\\1\\]\\]?d?o?', src)
        hgconst = None
        baseid = base = None
        for mb in re.finditer(re.escape(lib) + '(\\d+)\\]\\]=(\\d+) local', src):
            win = src[mb.start():mb.start() + 400]
            mh = re.search('local \\w+=\\(function\\(\\)local \\w+=\\{\\}for \\w+=1,\\S{1,60}?do \\w+\\[\\w+\\]=\\w+\\((\\d+)\\+\\w+\\)%256', win)
            if mh:
                baseid, base, hgconst = (mb.group(1), int(mb.group(2)), int(mh.group(1)))
                break
        if baseid is None:
            self.problems.append('doubles base/hg not found')
            return
        md = re.search('for \\w+=1,' + re.escape(lib) + baseid + '\\]\\] ?do ?local \\w+=5\\+\\(\\(\\w+-1\\)\\*8\\)local \\w+=' + '\\w+\\((' + re.escape(lib) + '\\d+\\]\\]),', src)
        if not md:
            self.problems.append('doubles decoder not found')
            return
        seedrefinner = md.group(1)
        seedref = 'n8[' + seedrefinner + ']' if seedrefinner.startswith('zk[') else 'O9[' + seedrefinner + ']' if seedrefinner.startswith('IF[') else seedrefinner
        seed = None
        mseed = re.search(re.escape(seedref) + '=((?:[^;]*?))(?=local |do |end |[;])', src)
        if mseed:
            expr = mseed.group(1)
            expr = re.sub('%hr|%hD|%eu', '%2147483647', expr)
            expr = re.sub('%0x100000000', '%4294967296', expr)
            expr = fold(expr)
            try:
                seed = int(eval(expr))
            except Exception:
                seed = None
        blob = None
        for mb2 in re.finditer(re.escape(lib) + '(\\d+)\\]\\]=(\\w+)\\(\\"([^\\"]+)\\"\\)', src):
            lit = mb2.group(3)
            if len(lit) < 400:
                continue
            if not re.search(re.escape(lib) + mb2.group(1) + '\\]\\]\\[', src[mb2.end():mb2.end() + 2500]):
                continue
            for alpha in self.vm.stringalphabets() + self.vm.tablealphabets():
                try:
                    dec = b91decode(lit, alpha)
                except Exception:
                    continue
                if len(dec) >= 4 + base * 8:
                    blob = dec
                    break
            if blob is not None:
                break
        if seed is None or blob is None:
            self.problems.append(f'doubles seed/blob unresolved (seed={seed}, blob={blob is not None})')
            return
        mixer = self.vm.mixer
        for jb in range(1, base + 1):
            key = (seed ^ mixer((hgconst + jb) % i31) % 256) & 255
            off = 4 + (jb - 1) * 8
            by = [blob[off + k] ^ key for k in range(8)]
            t8 = by[0] | by[1] << 8 | by[2] << 16 | by[3] << 24
            pc = by[4] | by[5] << 8 | by[6] << 16 | by[7] << 24
            sign = -1 if pc >> 31 & 1 else 1
            exp = pc >> 20 & 2047
            mant = pc & 1048575
            if exp == 2047:
                val = 0.0
            elif exp == 0:
                val = sign * (mant / 1048576.0 + t8 / 4503599627370496.0) * 2.0 ** (-1022)
            else:
                val = sign * (1.0 + mant / 1048576.0 + t8 / 4503599627370496.0) * 2.0 ** (exp - 1023)
            self.doubles[jb] = val

    def keylists2(self):
        src = self.src
        self.keylists = {}
        mm = re.search('local (\\w+)=\\{\\}do local (\\w+)=(\\w+)\\(\\)for (\\w+)=0,(\\w+)-1 do local (\\w+)=(\\w+)\\(\\)local (\\w+)=\\{\\}for (\\w+)=1,\\5 do local (\\w+)=(\\w+)\\(\\)local (\\w+)=(\\w+)\\((\\w+),(\\w+),\\w+\\+\\w+-1\\)\\w+=\\w+\\+\\w+ \\7\\[\\8\\]=\\w+ end \\1\\[\\4\\]=\\7 end end', src)
        blob = None
        cap = 1 << 20
        if not mm:
            ma = re.search('local (\\w+)=\\{\\}do local (\\w+)="([^"]{8,})"local (\\w+)=(\\w+)\\(\\2\\)', src)
            if ma:
                blob = ma.group(3)
                mcap = re.search('local \\w+=\\w+\\(' + re.escape(ma.group(2)) + '\\)\\w+=j7\\(\\w+,(\\d+)\\)', src[ma.start():ma.start() + 300])
                cap = int(mcap.group(1)) if mcap else 0
            else:
                return
        else:
            region = src[max(0, mm.start() - 4000):mm.start()]
            mblob = None
            for m3 in re.finditer('local (\\w+)="([^"]{200,})"', region):
                mblob = m3
            if mblob is None:
                self.problems.append('keylist blob not found')
                return
            blob = mblob.group(2)
            mcap = re.search('local \\w+=\\w+\\(' + re.escape(mblob.group(1)) + '\\)\\w+=\\w+\\(\\w+,(\\d+)\\)', region)
            cap = int(mcap.group(1)) if mcap else 1 << 20
        bestkls = None
        for alpha in self.vm.stringalphabets() + self.vm.tablealphabets():
            try:
                raw = b91decode(blob, alpha)
            except Exception:
                continue
            cands = [('raw', raw)]
            for c in ({cap} if cap else ()) + (1451, 1342, 1024, 4096, 65536, 1 << 20):
                try:
                    cands.append(('lz%d' % c, lz77decompress(raw, c)))
                except Exception:
                    pass
            for cname, dec in cands:
                pos = 0

                def r16():
                    nonlocal pos
                    if pos + 1 >= len(dec):
                        raise ValueError
                    v = dec[pos] | dec[pos + 1] << 8
                    pos += 2
                    return v
                try:
                    cnt = r16()
                    if cnt > 4096 or cnt < 1:
                        raise ValueError
                    kls = {}
                    for i in range(cnt):
                        n = r16()
                        if n > 512:
                            raise ValueError
                        lst = []
                        for _ in range(n):
                            ln = r16()
                            if ln > 256 or pos + ln > len(dec):
                                raise ValueError
                            lst.append(bytes(dec[pos:pos + ln]).decode('utf-8', 'replace'))
                            pos += ln
                        kls[i] = lst
                    score = (pos == len(dec), cnt >= 1, len(dec))
                    if bestkls is None or score > bestkls[0]:
                        bestkls = (score, kls, cname)
                except Exception:
                    continue
        if bestkls is not None:
            self.keylists = bestkls[1]

    def buildtables(self, P):
        pid = P['pid']
        P['uk'] = {}
        if self.ukb and len(P.get('uk_pairs', [])) >= 2:
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
        if self.vm.wptversion == 51:
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

    def normbody(self, body):
        b = body
        V = self.V
        pcname = V['pc']
        cont = self.vm.container
        for col in range(8):
            names = sorted(V['cols'].get(col, ()), key=len, reverse=True)
            for nm in names:
                if nm == V.get('opsarr') or nm == pcname or nm in ('R', 'R2'):
                    continue
                b = re.sub('(?<!\\w)' + re.escape(nm) + '\\[' + re.escape(pcname) + '(?![\\w])', f'COLTMP{col}[{pcname}', b)
        for col in range(8):
            sources = list(V['cols'].get(col, ()))
            tid = {c: t for t, c in V.get('colid2col', {}).items()}.get(col)
            if tid is not None:
                sources.append(re.escape(cont) + '\\[' + str(tid) + '\\]')
            for nm in sources:
                nmre = nm if nm.startswith(cont) else re.escape(nm)
                for am in re.finditer('(\\w{1,3})=' + nmre + '(?![\\w\\[])', b):
                    t = am.group(1)
                    b = re.sub('(?<!\\w)' + re.escape(t) + '\\[' + re.escape(pcname) + '(?![\\w])', f'COLTMP{col}[{pcname}', b)
        b = re.sub('COLTMP(\\d)', '@\\1', b)
        for tid, col in V.get('colid2col', {}).items():
            b = re.sub(re.escape(cont) + '\\[' + str(tid) + '\\]\\[' + re.escape(pcname) + '(?![\\w])', f'@{col}[{pcname}', b)
        for key, tag in (('regs', 'R'), ('uk', 'UK'), ('ue', 'UE'), ('uf', 'UF'), ('ufx', 'UFX'), ('upv', 'UPV'), ('cells', 'CELLS'), ('protos', 'PROTOS'), ('pool', 'POOL'), ('map', 'MAP')):
            if V.get(key):
                b = re.sub('(?<!\\w)' + re.escape(V[key]) + '(?=\\[|\\)|,)', tag, b)
        if V.get('map'):
            for am in re.finditer('(\\w{1,3})=' + re.escape(V['map']) + '(?![\\w\\[])', b):
                t = am.group(1)
                b = re.sub('(?<!\\w)' + re.escape(t) + '(?=\\[)', 'MAP', b)
        if V.get('dec'):
            dn = re.escape(V['dec'])
            b = re.sub('(?<!\\w)' + dn + '(?=\\()', 'DEC(', b)
            b = re.sub('type\\(' + dn + '\\)', 'type(DEC)', b)
            b = re.sub('and ' + dn + '\\)', 'and DEC)', b)
        if V.get('key'):
            b = re.sub('(?<=[,(])' + re.escape(V['key']) + '(?=[,)])', 'KEY', b)
        for key, tag in (('top', 'TOP'), ('uy', 'UY')):
            if V.get(key):
                b = re.sub('(?<!\\w)' + re.escape(V[key]) + '(?!\\w)', tag, b)
        b = re.sub('(?<!\\w)' + re.escape(pcname) + '(?!\\w)', 'PC', b)
        if V.get('envref'):
            b = b.replace(V['envref'], 'ENV')
        if V.get('xor'):
            b = re.sub('(?<!\\w)' + re.escape(V['xor']) + '\\(', 'XOR(', b)
        b = fold(b)
        return b

    def evalsym(self, sym, i, cols):
        if sym is None:
            return None
        if isinstance(sym, str):
            return sym
        if isinstance(sym, (int, float)):
            return sym
        k = getattr(sym, 'k', None)
        if k is None:
            return ('?', repr(sym))
        if k == 'lit':
            return sym.a
        if k == 'col':
            return cols[sym.a] or 0
        if k == 'xcol':
            m = self.evalsym(sym.b, i, cols)
            return ((cols[sym.a] or 0) ^ m & 255) & 255
        if k == 'bin':
            op = sym.b
            l = self.evalsym(sym.a, i, cols)
            r = self.evalsym(sym.c, i, cols)
            if l is None or r is None:
                return None
            try:
                if op == '+':
                    return l + r
                if op == '-':
                    return l - r
                if op == '*':
                    return l * r
                if op == '/':
                    return l / r
                if op == '%':
                    return l % r
                if op == '^':
                    return l ** r
                if op == 'xor':
                    return (l ^ r) & 4294967295
                if op == '..':
                    return str(l) + str(r)
                if op == '==':
                    return l == r
                if op == '~=':
                    return l != r
                if op == '<':
                    return l < r
                if op == '<=':
                    return l <= r
                if op == '>':
                    return l > r
                if op == '>=':
                    return l >= r
                if op == 'and':
                    return r if l not in (None, False) else l
                if op == 'or':
                    return l if l not in (None, False) else r
            except Exception:
                return None
        if k == 'un':
            v = self.evalsym(sym.b, i, cols)
            if sym.a == 'not':
                return not v
            if sym.a == '-':
                return -v
            if sym.a == '#':
                return len(v) if v is not None else None
        if k == 'inl':
            uc = self.evalsym(sym.b, i, cols)
            if uc is None:
                return None
            if 0 <= uc < len(self.vm.inlinemap):
                sid = self.vm.inlinemap[uc]
                if sid != 65535 and sid in self.vm.strings:
                    return self.vm.strings[sid]
            return None
        if k == 'pool':
            uc = self.evalsym(sym.a, i, cols)
            return self.doubles.get(uc)
        if k == 'env':
            return ('ENVNAME', self.evalsym(sym.a, i, cols))
        if k == 'reg':
            idx = self.evalsym(sym.a, i, cols)
            return ('R', idx)
        if k == 'pc':
            return ('PC',)
        if k == 'top':
            return ('TOP',)
        if k == 'uk':
            return ('UK',)
        if k == 'uf':
            return ('UF',)
        return ('?', sym.k)

    def classify(self):
        self.ops = {}
        self.unknown = []
        for op, body in self.vm.handlers.items():
            nb = self.normbody(body)
            kind, extra = self.kindregex(nb)
            semop = {'kind': kind, 'extra': extra, 'nb': nb}
            try:
                semop['cspecs'] = constspecs(nb)
            except Exception:
                semop['cspecs'] = []
            try:
                semop['spec'] = buildspec(self, op) if False else {'sbx': sbxpairs(nb)}
            except Exception:
                semop['spec'] = {'sbx': []}
            ast = parselua(nb)
            if ast is not None:
                self.constordinal = 0
                st = normalizer(self).run(ast)
                semop['state'] = st
            self.ops[op] = semop
            if kind == 'UNKNOWN':
                self.unknown.append(op)

    def kindregex(self, nb):

        def H(p):
            return re.search(p, nb) is not None
        w0 = 'R\\[@0\\[PC\\]\\]'
        w1 = 'R\\[@1\\[PC\\]\\]'
        w2 = 'R\\[@2\\[PC\\]\\]'
        w3 = 'R\\[@3\\[PC\\]\\]'
        if re.search('if \\w+==0 then return \\w+\\((R|\\w+),\\w+,TOP-1\\)elseif \\w+==1 then return else', nb):
            return ('RETURN', {})
        if H('return \\w+\\(R,') and H('TOP-1') and (not H('R\\[@0\\+')):
            return ('RETURN', {})
        if H("\\['n'\\]") and H('=\\{\\}') and (not H('TOP=\\w+\\+\\w+')):
            return ('VARARG_PREP', {})
        if H("\\['n'\\]=\\w+-\\w+|\\[zD\\]=\\w+-\\w+"):
            if H('TOP=\\w+\\+\\w+'):
                return ('VARARG_EXPAND', {})
            return ('VARARG_PREP', {})
        if H('R\\[@0\\+\\w+\\]=nil TOP=\\w+\\+\\w+'):
            return ('VARARG_EXPAND', {})
        if H('UE\\[') or H('PC\\+UY') or H('\\(PC\\+UY\\)'):
            m = re.search('\\w+=(not\\(.*?\\)|.*?)(?:if \\w+ then|\\w+=\\w+ and)', nb)
            cond = ''
            m2 = re.search('=not\\((.*?)\\)', nb) or re.search('\\w+=(.*?)if \\w+ then', nb)
            if m2:
                cond = m2.group(1)
            if re.search('\\]=DEC|' + w1 + '\\]=\\w+.*MAP|MAP\\[', nb) and ('~=' in cond or '==' in cond):
                return ('CMP_CONST', {'op': '~=' if '~=' in cond else '=='})
            if 'not(' in cond:
                if '~=' in cond:
                    return ('CMP', {'op': '=='})
                if '<=' in cond:
                    return ('CMP', {'op': '>'})
                if '<' in cond:
                    return ('CMP', {'op': '>='})
                if '==' in cond:
                    return ('CMP', {'op': '~='})
            if '~=' in cond:
                return ('CMP', {'op': '~='})
            if '<=' in cond:
                return ('CMP', {'op': '<='})
            if '<' in cond:
                return ('CMP', {'op': '<'})
            if '==' in cond:
                return ('CMP', {'op': '=='})
            return ('CMP', {'op': '?'})
        if H('PC=UK\\[PC\\]'):
            if H(w0 + '=' + w1) and H('UP=not'):
                return ('MOVE_TEST', {'pol': 'falsy'})
            if H('R\\[@0\\[PC\\]\\]=\\(@1\\[PC\\]~=0\\)'):
                return ('BOOL_TEST', {})
            if H('==nil or not'):
                return ('TEST', {'pol': 'falsy'})
            if H('UP=not\\(' + w0 + '\\)'):
                return ('TEST', {'pol': 'falsy'})
            if H('~=nil and'):
                return ('TEST', {'pol': 'truthy'})
            if 'UPV' in nb:
                return ('UPV_GETTABLEK_TEST', {})
            if 'DEC(' in nb and H('UP=not'):
                return ('GETTABLEK_TEST', {})
            return ('JMP', {})
        if H('>0 and \\w+<=\\w+\\)or\\(\\w+<=0 and \\w+>=\\w+\\)'):
            if H('R\\[@0\\+2\\]=\\w+\\+\\w+|R\\[@0\\+2\\]=\\w+%\\w+'):
                return ('FORLOOP', {})
            return ('FORPREP', {})
        if H('__iter') or re.search('R\\[\\w+\\],R\\[\\w+\\+1\\],R\\[\\w+\\+2\\]=', nb):
            return ('TFORPREP', {})
        if re.search('~=nil then.{0,80}R\\[\\w+\\+2\\]=\\w+', nb) and H('UF\\[PC\\]') and H('UFX\\[\\w+\\]'):
            return ('TFORLOOP', {})
        if H('UFX\\[UF\\[PC\\]\\+\\d+\\+\\w+\\]') and H('R\\[@\\d\\[PC\\]\\]=\\(@\\d\\[PC\\]~=0\\)'):
            return ('BOOL_JMP', {})
        if 'PROTOS[' in nb:
            if H('R\\[@\\d\\[PC\\]\\]\\[') and 'DEC' in nb:
                return ('CLOSURE_SETFIELD', {})
            return ('CLOSURE', {})
        if H('\\[PC\\+1\\]==\\d+ or \\w+\\[PC\\+1\\]==\\d+ or \\w+\\[PC\\+1\\]==\\d+ then'):
            return ('LOADLIB', {})
        if H('for \\w+=0,\\w+-1 do \\w+\\[\\w+\\+\\w+\\]=R\\[\\w+\\+\\w+\\]'):
            return ('SETLIST', {})
        if H('UPV\\[\\w+\\+1\\]=') and 'R[' in nb:
            return ('SETUPVAL', {})
        if 'UPV[' in nb and 'CELLS' not in nb and (not H('UPV\\[\\w+\\+1\\]=')):
            if H('UP=not') and H('PC=UK'):
                return ('UPV_GETTABLEK_TEST', {})
            if H('TOP=') or H('zg=TOP'):
                return ('CALL_UPVAL', {})
            if H('\\]or nil') and H('__index|DEC\\(\\d') and (H(w0 + '=\\w+\\[\\w+\\]$') is False):
                pass
            if re.search('U\\w+=\\w+ and \\w+\\[\\w+\\]or \\w+|\\[DEC\\(', nb):
                if H('R\\[@\\d\\[PC\\]\\]\\['):
                    return ('GETUPVAL_GETTABLEK', {})
                return ('GETUPVAL', {})
            if H('zj\\(|Iv\\(') and H('==zM'):
                return ('GETUPVAL', {})
            if H(w0 + '=\\w+$') and 'DEC' not in nb and ('MAP' not in nb):
                return ('GETUPVAL', {})
            if re.search('R\\[\\w+\\]=\\w+$', nb) and 'MAP' not in nb and ('ENV' not in nb) and (not H('TOP')):
                return ('GETUPVAL', {})
            if H(w0 + '=') and H('n8\\[zk\\[17816\\]\\]|O9\\[IF\\[41886\\]\\]'):
                return ('GETUPVAL', {})
        if re.search('for \\w+,\\w+ in [\\w\\[\\]]+\\(CELLS\\)', nb):
            return ('CLOSE', {})
        callish = H('TOP=\\w+\\+\\w+') or H('zg=TOP') or H('zh=true') or H('for \\w+=1,\\w+ do R\\[@0\\+\\w+-1\\]=')
        if callish:
            if 'UPV' in nb and 'CELLS' not in nb:
                return ('CALL_UPVAL', {})
            if 'ENV[' in nb:
                if H('R\\[@0\\+1\\]=' + w1) or H('R\\[@0\\+2\\]=DEC') or H('R\\[@0\\+1\\]=DEC'):
                    return ('CALL_SELF', {})
                return ('CALL_GLOBAL', {})
            if H('R\\[@0\\+1\\]\\[') or (H('R\\[@0\\+2\\]=\\w+$') and H('\\[DEC')) or (H('\\[@0\\+1\\]=\\w+$') and H('\\[DEC\\(')):
                return ('CALL_SELF', {})
            if H('R\\[@0\\+1\\]=DEC') or H('R\\[@0\\+2\\]=DEC'):
                return ('CALL_CONST', {})
            return ('CALL', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) == 1 and re.search('if \\w+ then.{0,40}\\w+\\[\\w+\\]=R\\[@\\d\\[PC\\]\\]', nb) and ('UPV' not in nb) and ('ENV' not in nb):
            return ('SETTABLEK_REGVAL', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) == 1 and re.search('if \\w+ then \\w+\\[\\w+\\]=\\w+ end', nb) and ('UPV' not in nb) and ('ENV' not in nb) and (not re.search('R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\]', nb)):
            return ('SETTABLEK', {})
        if H('ENV\\[\\w+\\]=') and 'R[' in nb:
            return ('SETGLOBAL', {})
        if 'UPV[' in nb and 'MAP[' in nb and ('ENV' not in nb):
            if re.search('\\w+\\[\\w+\\]=R\\[@\\d\\[PC\\]\\]|R\\[@\\d\\[PC\\]\\]=\\w+\\[\\w+\\]', nb):
                return ('UPV_GETTABLEK_SET', {})
            return ('GETUPVAL_GETTABLEK', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) == 2 and 'UPV' not in nb and ('ENV' not in nb):
            if re.search('=\\w+\\[\\w+\\].*?R\\[@\\d\\[PC\\]\\]=\\w+', nb) and re.search('\\w+\\[\\w+\\]=\\w+($|\\s|\\.)', nb):
                if re.search('\\w+\\[\\w+\\]=R\\[@\\d\\[PC\\]\\]|=R\\[@\\d\\[PC\\]\\]$', nb) and re.search('R\\[@\\d\\[PC\\]\\]=\\w+.*\\w+\\[\\w+\\]=\\w+', nb):
                    return ('GETTABLEK_SETTABLEK', {})
                return ('GETTABLEK2', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) == 2 and 'UPV' not in nb and ('ENV' not in nb):
            return ('GETTABLEK2', {})
        if H('=ENV') and H('R\\[@\\d\\[PC\\]\\]=U?\\w+$') is not None and ('gmatch' not in nb):
            return ('GETGLOBAL', {})
        if H('U\\w+=ENV\\b') and 'MAP' in nb and (not H('ENV\\[\\w+\\]=R')):
            return ('GETGLOBAL', {})
        if H('gmatch') and H('tonumber'):
            return ('GETIMPORT_DOTTED', {})
        if H('=ENV\\[\\w+\\]\\[\\w+\\]\\['):
            return ('GETIMPORT3', {})
        if H('=ENV\\[\\w+\\]\\['):
            return ('GETIMPORT2', {})
        if H('for \\w+,\\w+ in \\w+\\([\\w\\[\\]]+\\[\\w+\\]\\) do \\w+\\[\\w+\\]=false end') and H('R\\[@\\d\\[PC\\]\\]=\\w+$'):
            return ('NEWTABLE_KEYS', {})
        if H('R\\[\\w+\\]=\\{\\}') and len(nb) < 120:
            return ('NEWTABLE', {})
        if H('\\w+\\[\\w+\\]=false end') and H('=\\{\\}'):
            return ('NEWTABLE_KEYS_CONST', {})
        if H(w0 + '=\\w+ and \\w+\\[\\w+\\]or nil') and 'UPV' not in nb:
            return ('GETTABLEK', {})
        if H(w0 + '=\\w+\\[\\w+\\]$') and 'DEC(' in nb:
            return ('GETTABLEK', {})
        if re.search('U\\w+=\\w+ and \\w+\\[\\w+\\]or nil', nb) and 'UPV' not in nb:
            return ('GETTABLEK', {})
        if H('R\\[@0\\+1\\]=\\w+$') and 'DEC(' in nb and (H('R\\[@0\\+1\\]=' + w1) is False):
            return ('SELF', {})
        if H('R\\[@0\\+1\\]=' + w1) and 'DEC(' in nb:
            return ('SELF', {})
        if re.search('R\\[\\w+\\]=\\w+ R\\[\\w+\\+1\\]=\\w+', nb) and 'MAP' in nb and ('UPV' not in nb) and ('ENV' not in nb):
            return ('SELF', {})
        if H('R\\[@\\d\\[PC\\]\\]\\[\\w+\\]=\\w+') and 'DEC(' in nb:
            return ('SETTABLEK', {})
        if H('\\[\\w+\\]=\\w+ if \\w+ then') and 'DEC(' in nb and H('R\\[@\\d\\[PC\\]\\]\\['):
            return ('SETTABLEK', {})
        if H('if \\w+ then \\w+\\[\\w+\\]=\\w+ end') and 'DEC(' in nb and (not H('UPV')):
            return ('SETTABLEK', {})
        if H('\\[R\\[@\\d\\[PC\\]\\]\\]=R\\[|U\\w+=R\\[@\\d\\[PC\\]\\] .*?\\w+\\[U\\w+\\]=U?\\w+$') or (H('\\]\\[\\w+\\]=\\w+$') and H('R\\[@\\d\\[PC\\]\\]=\\w+\\[\\w+\\]') is False and H('if \\w+ then \\w+\\[') and ('DEC' not in nb)):
            return ('SETTABLE_RR', {})
        if H(w1 + '\\[R\\[@2\\[PC\\]\\]\\]=' + w0) or H('if \\w+ then \\w+\\[R\\[@\\d\\[PC\\]\\]\\]='):
            return ('SETTABLE_RR', {})
        if H('R\\[@\\d\\[PC\\]\\]\\[@\\d\\[PC\\]\\+1\\]=R\\[|\\[@\\d\\[PC\\]\\+1\\]=R\\[@2\\[PC\\]\\]'):
            return ('SETTABLE_INT', {})
        if H('R\\[@\\d\\[PC\\]\\]=\\w+\\[\\w+\\]') and re.search('\\w+=@\\d\\[PC\\]\\+1', nb):
            return ('GETTABLE_INT', {})
        if H(w0 + '=' + w1 + '\\[') and 'DEC' not in nb and ('UPV' not in nb):
            return ('GETTABLE_RR', {})
        if re.search('R\\[@\\d\\[PC\\]\\]=\\w+\\[\\w+\\]($|\\s)', nb) and re.search('\\w+=R\\[@\\d\\[PC\\]\\]', nb) and ('DEC' not in nb) and ('MAP' not in nb):
            return ('GETTABLE_RR', {})
        if H('if \\w+ then \\w+\\[\\w+\\]=\\w+ end') and re.search('\\w+=R\\[@\\d\\[PC\\]\\]', nb) and ('DEC' not in nb):
            return ('SETTABLE_RR', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) >= 2 and re.search('if \\w+ then \\w+\\[\\w+\\]=\\w+ end', nb) and ('UPV' not in nb) and ('ENV' not in nb):
            return ('SETTABLEK2', {})
        if 'POOL[' in nb:
            if re.search(w0 + '=\\\\w+[-+*/%^].*POOL', nb) or re.search(w0 + '=' + w1 + '[-+*/%^]', nb):
                return ('ARITH_CONST', {})
            if H(w0 + '=POOL') or re.search('R\\[\\w+\\]=POOL', nb):
                return ('LOADNUM', {})
        if H('UF\\[PC\\]') and H('UFX\\[\\w+\\]') and H('\\(@\\d\\[PC\\]~=0\\)') and (not re.search('>0 and', nb)):
            return ('BOOL_JMP', {})
        if '32768' in nb:
            if len(re.findall('R\\[@\\d\\[PC\\]\\]=\\w+$|R\\[@\\d\\[PC\\]\\]=\\w+ ', nb)) >= 2 and len(re.findall('\\*256\\)', nb)) >= 2 and ('R[' not in nb.split('if')[0]):
                return ('LOADN16_2', {})
            if re.search('R\\[\\w+\\]=\\w+\\*\\w+ else R\\[\\w+\\]=\\w+\\*\\w+', nb):
                return ('ARITH_SBX', {})
            if H('\\*65536|16777216'):
                return ('LOADN32', {})
            m = re.search('\\w+=(@\\d)\\[PC\\]\\+\\((@\\d)\\[PC\\]\\*256\\)', nb)
            if m:
                return ('LOADN16', {})
            return ('SBX_OTHER', {})
        if H('2\\^-149|pow\\(2,-149\\)|4503599627370496|2,-1022'):
            return ('LOADF32', {})
        if H('\\(@\\d\\[PC\\]~=0\\)') and re.search('R\\[@\\d\\[PC\\]\\]=\\w+', nb):
            return ('LOADBOOL', {})
        if H('R\\[\\w+\\]=nil') or H('R\\[@\\d\\[PC\\]\\]=nil') or (re.search('\\w+=nil ', nb) and re.search('R\\[@\\d\\[PC\\]\\]=\\w+$', nb) and (len(nb) < 160)):
            return ('LOADNIL', {})
        if H('while \\w+~=0 do') and H('R\\[\\(\\w+\\+\\w+\\)\\]=nil'):
            return ('LOADNIL_MASK', {})
        if H('R\\[@\\d\\[PC\\]\\]=not ' + w1):
            return ('NOT', {})
        if H('R\\[@\\d\\[PC\\]\\]=-') or (H('U\\w+=R\\[@1\\[PC\\]\\]') and H('R\\[@\\d\\[PC\\]\\]=-U\\w+')):
            return ('NEG', {})
        if H('R\\[@\\d\\[PC\\]\\]=#'):
            return ('LEN', {})
        if H('for \\w+=@1\\[PC\\],@2\\[PC\\] do') or (H("''") and H('\\.\\.')):
            return ('CONCAT', {})
        m = re.search(w0 + '=\\(?\\w+\\)?([-+*/%^])\\(?\\w+', nb) or re.search(w0 + '=\\(' + w1 + '\\)([-+*/%^])', nb) or re.search(w0 + '=' + w1 + '([-+*/%^])' + w2, nb)
        if m:
            op = m.group(1)
            if H('if @\\d\\[PC\\]~=0 then') and H('else R\\[@0\\[PC\\]\\]='):
                return ('ARITH_SWAP', {'op': op})
            return ('ARITH', {'op': op})
        if H('fmod') or (H('getmetatable|34293|33046') and H('/') and H('R\\[@\\d\\[PC\\]\\]=\\w+\\(')):
            return ('IDIV', {})
        if H('U\\w+=R\\[@1\\[PC\\]\\]U?\\w*=\\w+ if \\w+ then \\w+=' + w2 + ' end'):
            return ('AND', {})
        if H('if \\w+ then \\w+=' + w2 + ' else') and H(w1):
            return ('OR', {})
        if len(re.findall('MAP\\[[^\\]]+\\],KEY\\)', nb)) == 1 and re.search('R\\[@\\d\\[PC\\]\\]=\\w+(\\[\\d+\\])?', nb) and ('ENV' not in nb) and (not re.search('R\\[@\\d\\[PC\\]\\]\\[', nb)) and (not re.search('UE\\[|PC\\+UY', nb)) and (not re.search('R\\[@\\d\\[PC\\]\\]=R\\[@', nb)) and (not re.search('if \\w+ then \\w+\\[\\w+\\]=\\w+ end', nb)) or H(w0 + '=DEC'):
            if H('R\\[@\\d\\[PC\\]\\]\\[') and 'DEC' in nb:
                return ('SETTABLEK', {})
            return ('LOADK', {})
        if re.search('U\\w+=DEC', nb) and re.search('\\[\\w+\\]=\\w+ if', nb):
            return ('SETTABLEK', {})
        if re.search('R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\].*R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\]', nb):
            return ('MOVE2', {})
        if re.search('R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\]', nb) and re.search('MAP\\[[^\\]]+\\],KEY\\)', nb):
            return ('MOVE_LOADK', {})
        if H('R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\]$') or re.search('R\\[@\\d\\[PC\\]\\]=R\\[@\\d\\[PC\\]\\] ', nb):
            return ('MOVE', {})
        if re.search('=\\{R\\[@\\d\\[PC\\]\\]\\}R?\\[@\\d\\[PC\\]\\]=\\w+\\[1\\]', nb):
            return ('MOVE', {})
        if not re.search('R\\[|DEC|MAP|POOL|ENV\\[|UPV\\[|TOP|return|UFX\\[|UK\\[', nb):
            return ('NOP', {})
        if H('MM=true|Q2=true') and (not re.search('R\\[@\\d\\[PC\\]\\]=\\w', nb)):
            if not re.search('MAP\\[|POOL\\[|ENV\\[[^\\]]*\\]=R', nb):
                return ('NOP', {})
        return ('UNKNOWN', {})
