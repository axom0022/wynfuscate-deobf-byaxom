from __future__ import annotations
import re
from .luaparse import parselua
from .util import b91decode, luaunescape

dxname = {
    50594: 'select', 65393: 'floor', 37856: 'math', 64815: 'pairs', 58054: 'pack',
    8763: 'getmetatable', 63363: 'error', 54546: 'mkclosure', 6527: 'templates',
    12777: 'env', 24047: 'xor', 23835: 'r', 51400: 'r2', 51199: 'r3', 62929: 'ek',
    61567: 'strtab', 46733: 'string', 56165: 'ir', 15160: 'setfenv', 59996: 'protowrap',
    55510: 'error', 25377: 'variant', 64901: 'tamperstate', 25319: 'tampercheck',
    20958: 'tamperkey', 60910: 'char', 37725: 'bytes2str', 9034: 'tkey',
    38670: 'pack2', 24311: 'mulmod', 58638: 'setmetatable', 53480: 'pk',
    12661: 'blobstr', 17211: 'gbstore', 39080: 'tamper1', 55679: 'tamper2',
    56606: 'tamper3', 46718: 'tamper4', 33290: 'tamper5',
}

guards = [
    r"local Qo=dQ local tO=o8\[dx\[64901\]\]if tO and o8\[dx\[25319\]\]\(tO,o8\[dx\[dN\[\d+\]\]\]\)then o8\[dx\[55679\]\]=nil o8\[dx\[39080\]\]\(tO,o8\[dx\[dN\[\d+\]\]\],o8\[dx\[56606\]\]\)tP=nil R6=2 end ",
    r"local tO=o8\[dx\[64901\]\]local \w+=tO and o8\[dx\[25319\]\]\(tO,o8\[dx\[dN\[\d+\]\]\]\)if \w+ then local \w+=5\+\(\(Rq\[tH\]or 0\)\+\(Rl\[tH\]or 0\)\+\(RY\[tH\]or 0\)\)%46 local \w+=tH\+\w+ local \w+=#Rc if \w+ and \w+>0 and \w+>\w+ then \w+=\w+-\(\w+%3\)end Rc\[\w+\]=149 o8\[dx\[55679\]\]=nil end ",
    r"local tO=o8\[dx\[64901\]\]if tO and o8\[dx\[25319\]\]\(tO,o8\[dx\[dN\[\d+\]\]\]\)then [^e]*? end ",
    r"local \w+=Rl if type\(\w+\)~='table'then \w+=Ih\[5102\]end if type\(\w+\)~='table'then \w+=\{\}end ",
    r"local \w+=RY if type\(\w+\)~='table'then \w+=Ih\[8959\]end if type\(\w+\)~='table'then \w+=\{\}end ",
    r"\w+=eK if type\(\w+\)~='table'then \w+=o8\[dx\[62929\]\]end if type\(\w+\)~='table'then \w+=\{\}end ",
    r"if type\(\w+\)~='table'then \w+=Ih\[\d+\]end if type\(\w+\)~='table'then \w+=\{\}end ",
    r"local (?:KG,Kx,KZ,KL,KJ,Kz,KN,KT,K3,K6,K9|Kx,KZ,KL,KN|KG,Kx,KZ,KL,KN|KG,Kx,KZ,KL,KJ,Kz,KN|KG,Kx,KZ,KL,KN,KJ,Kz,KT,K3,K6)(?:,\w+)* ",
    r"(?:KL,KJ,Kz,K3,K6|KL,KJ,Kz)=nil(?::nil)* ",
    r"do local \w+=o8\[dx\[dN\[\d+\]\]\];local \w+=o8\[dx\[dN\[\d+\]\]\];local \w+=o8\[dx\[dN\[\d+\]\];local \w+=o8\[dx\[dN\[\d+\]\] ",
    r"if not ds\.Yn then ds\.Yn=true local Kv=\(ds\.KZ or 0\)ds\.KZ=Kv\+1 end ",
    r"local Qo=dQ ",
    r"local jK=tF or 0 ",
]


def denoise(body):
    out = body
    for pat in guards:
        out = re.sub(pat, '', out)
    return out


def unesc(s):
    if s.startswith('"') and s.endswith('"'):
        s = s[1:-1]
    return re.sub(r'\\(\d{1,3})', lambda m: chr(int(m.group(1))), s)


class g3sem:

    def __init__(self, vm):
        self.vm = vm
        self.handlers = {op: denoise(b) for op, b in vm.handlers.items()}
        self.asts = {}
        for op, body in self.handlers.items():
            try:
                self.asts[op] = parselua(body)
            except Exception:
                self.asts[op] = None
        self.strings = {k: (v.decode('latin-1') if isinstance(v, bytes) else v)
                        for k, v in vm.strings.items()}
        self.ek = self.buildek(vm)
        self.templates = {}
        self.problems = []
        self.junkops = set()
        strong = ('setreg', 'setfield', 'jump', 'return', 'callmulti', 'newtbl',
                  'closure', 'vararg-prep', 'vararg-use', 'close', 'concat',
                  'setglobal', 'stdload', 'settop')

        def strongeff(eff):
            for e in eff:
                if e[0] in ('alt', 'guard'):
                    inner = e[2] if e[0] == 'guard' else (e[2] + e[3])
                    if strongeff(inner):
                        return True
                if e[0] in strong:
                    return True
            return False
        for op in self.handlers:
            if self.asts.get(op) is None:
                continue
            found = False
            for pr in vm.protos:
                hit = False
                for i, o in enumerate(pr['ops']):
                    if o == op:
                        hit = True
                        break
                if not hit:
                    continue
                for pc in range(1, pr['n'] + 1):
                    if pr['ops'][pc - 1] != op:
                        continue
                    eff = self.decoderaw(pr, pc)
                    if strongeff(eff):
                        found = True
                        break
                if found:
                    break
            if not found:
                self.junkops.add(op)

    def buildek(self, vm):
        mega = vm.findmega()
        text = luaunescape(mega.group(2)).decode('latin-1')
        sub = text[70194 - 1:77181]
        for alpha in vm.stringalphabets() + vm.tablealphabets():
            try:
                raw = b91decode(sub, alpha)
            except Exception:
                continue
            if len(raw) >= 5712:
                return [raw[i * 2] * 256 + raw[i * 2 + 1] for i in range(2856)]
        return []

    def decoderaw(self, P, pc):
        op = P['ops'][pc - 1]
        ast = self.asts.get(op)
        if ast is None:
            return [('note', f'parse failed for op {op}')]
        it = interp(self, P, pc)
        try:
            it.run(ast)
        except Exception:
            return it.effects
        return normalize(it.effects)

    def decode(self, P, pc):
        op = P['ops'][pc - 1]
        body = self.handlers.get(op)
        if body is None:
            return [('note', f'no handler for op {op}')]
        if body and re.search(r"if R6>R9 then tP\[R3\]=''", body) and r'R7=tP\[R5\]\.\.R7' in body:
            return [('concat', P['regs'][0].get(pc) or 0, P['regs'][1].get(pc) or 0,
                     P['regs'][2].get(pc) or 0)]
        if body and 'tP[(R3+R9)]=nil' in body:
            return [('close', P['regs'][0].get(pc) or 0)]
        if op in self.junkops:
            return []
        ast = self.asts.get(op)
        if ast is None:
            return [('note', f'parse failed for op {op}')]
        it = interp(self, P, pc)
        try:
            it.run(ast)
        except RecursionError:
            return it.effects + [('note', 'recursion')]
        except Exception as e:
            return it.effects + [('note', f'{type(e).__name__}: {e}')]
        return normalize(it.effects)


def normalize(effects):
    out = []
    for e in effects:
        if e[0] == 'alt':
            cond, th, el = e[1], e[2], e[3]
            th = normalize(th)
            el = normalize(el)
            if len(th) == 1 and th[0][0] == 'jump' and not el:
                out.append(('cjump', cond, th[0][1]))
            elif len(el) == 1 and el[0][0] == 'jump' and not th:
                out.append(('cjump', ('un', 'not', cond), el[0][1]))
            elif not el:
                out.append(('guard', cond, th))
            else:
                out.append(('alt', cond, th, el))
        else:
            out.append(e)
    return out


class interp:

    def __init__(self, sem, P, pc):
        self.sem = sem
        self.P = P
        self.pc = pc
        self.cols = {}
        self.regknown = {}
        self.effects = []
        self.depth = 0
        g3 = P.get('g3')
        for i, c in enumerate((8727, 5102, 8959, 1228, 1514, 6151, 6134)):
            self.cols[c] = (g3.cols[c].get(pc) or 0) if g3 else 0
        self.cols[4998] = P['ops'][pc - 1]
        self.env = {
            'tH': ('num', pc), 'Ih': ('ih',), 'tP': ('tp',), 'tS': ('ts',),
            'tF': ('top',), 'tr': ('tr',), 'tn': ('tn',), 'tO': ('cells',),
            'gb': ('gb',), 'eK': ('ek',), 'lU': ('num', 1696633738),
            'Rq': ('cvar', 8727), 'Rl': ('cvar', 5102), 'RY': ('cvar', 8959),
            'Rc': ('cvar', 4998), 'RT': ('uk',), 'RZ': ('z',), 'RL': ('l',),
            'r': ('fn', 'r'), 'dA': ('fn', 'xor'), 'dI': ('fn', 'typeof'),
            'dQ': ('fn', 'expand'), 'dq': ('fn', 'floor'), 'dc': ('fn', 'mulmod'),
            'dt': ('str', 'function'), 'dg': ('str', 'string'),
            'dD': ('str', 'table'), 'dW': ('str', 'number'), 'dR': ('str', 'boolean'),
            'di': ('str', 'nil'), 'oL': ('lib', 'math'), 'oT': ('lib', 'string'),
            'de': ('lib', 'table'), 'o8': ('o8',), 'ds': ('nil',),
            'dM': ('nil',), 'dE': ('num', 0), 'dC': ('bool', False),
            'tv': ('bool', False), 'tu': ('bool', False), 'dK': ('num', 0),
            'th': ('unk', 'argc'), 'pw': ('unk', 'pw'), 'cp': ('num', 2147483647),
            'cU': ('num', 4294967296), 'dx': ('dxt',), 'dN': ('dnt',),
            'type': ('fn', 'typeof'), 'pairs': ('fn', 'pairs'),
            'select': ('fn', 'select'), 'rawget': ('fn', 'rawget'),
            'tostring': ('fn', 'tostring'), 'tonumber': ('fn', 'tonumber'),
            'unpack': ('fn', 'unpack'), 'ipairs': ('fn', 'ipairs'),
            'next': ('fn', 'next'), 'setmetatable': ('fn', 'setmetatable'),
            'getfenv': ('fn', 'getfenv'), 'pcall': ('fn', 'pcall'),
            'En': ('fn', 'enlen'), 'lU': ('num', 1696633738),
            'jW': ('unk', 'jW'), 'jD': ('unk', 'jD'), 'jg': ('unk', 'jg'),
        }

    def run(self, ast):
        self.block(ast)

    def block(self, stmts):
        for st in stmts:
            self.stmt(st)

    def stmt(self, st):
        if self.depth > 60:
            return
        k = st[0]
        if k == 'assign':
            self.assign(st[1], self.ev(st[2]))
        elif k == 'local':
            names, exprs = st[1], st[2]
            if len(exprs) == 1 and len(names) > 1:
                v = self.ev(exprs[0])
                if v[0] == 'call':
                    for i, n in enumerate(names):
                        self.env[n] = ('callres', v, i)
                    return
                if v[0] == 'range':
                    for i, n in enumerate(names):
                        self.env[n] = ('rngres', v, i)
                    return
            for i, n in enumerate(names):
                self.env[n] = self.ev(exprs[i]) if i < len(exprs) else ('nil',)
        elif k == 'if':
            cond = self.ev(st[1])
            t = truth(cond)
            if t is True:
                self.block(st[2])
            elif t is False:
                for c, b in st[3]:
                    if truth(self.ev(c)) is True:
                        self.block(b)
                        return
                if st[4]:
                    self.block(st[4])
            elif istypetest(cond):
                self.depth += 1
                self.block(st[2])
            else:
                self.depth += 1
                saved = (dict(self.env), {k2: v for k2, v in self.regknown.items()})
                e0 = len(self.effects)
                self.block(st[2])
                thenf = self.effects[e0:]
                del self.effects[e0:]
                self.env, self.regknown = saved
                for c, b in st[3]:
                    if truth(self.ev(c)) is True:
                        self.block(b)
                        elsf = self.effects[e0:]
                        del self.effects[e0:]
                        self.effects.append(('alt', cond, thenf, elsf))
                        return
                if st[4]:
                    self.block(st[4])
                elsef = self.effects[e0:]
                del self.effects[e0:]
                self.env, self.regknown = saved
                self.effects.append(('alt', cond, thenf, elsef))
        elif k == 'while':
            t = truth(self.ev(st[1]))
            if t is True:
                self.depth += 1
                self.block(st[2])
            elif t is None:
                mark = ('symwhile', len(self.effects))
                self.effects.append(mark)
                self.depth += 1
                self.block(st[2])
                if self.effects and self.effects[-1] is mark:
                    self.effects.pop()
        elif k == 'fornum':
            self.fornum(st)
        elif k == 'forin':
            self.forin(st)
        elif k == 'massign':
            targets, exprs = st[1], st[2]
            if len(exprs) == 1 and len(targets) > 1:
                v = self.ev(exprs[0])
                for i, t in enumerate(targets):
                    self.assign(t, ('callres', v, i) if v[0] == 'call' else
                                ('rngres', v, i) if v[0] == 'range' else v)
                return
            for i, t in enumerate(targets):
                self.assign(t, self.ev(exprs[i]) if i < len(exprs) else ('nil',))
        elif k == 'return':
            vals = [self.ev(e) for e in st[1]]
            self.returnstat(vals)
        elif k == 'callstat':
            v = self.ev(st[1])
            if isinstance(v, tuple) and v[0] == 'call':
                self.effects.append(('callstat', v[1], v[2]))
        elif k == 'do':
            self.block(st[1])
        elif k == 'break':
            self.effects.append(('note', 'break'))
        elif k == 'repeat':
            self.block(st[1])

    def fornum(self, st):
        _, v, a, b, c, body = st
        av, bv = self.ev(a), self.ev(b)
        step = self.ev(c) if c else ('num', 1)
        if self.num(av) and self.num(bv) and self.num(step) and step[1] != 0:
            i = av[1]
            if step[1] > 0:
                rng = range(i, bv[1] + 1, step[1])
            else:
                rng = range(i, bv[1] - 1, step[1])
            if len(rng) > 4000:
                return
            for i2 in rng:
                self.env[v] = ('num', i2)
                self.block(body)
            return
        if len(body) == 1 and body[0][0] == 'assign' and self.num(a):
            tgt, srcv = body[0][1], body[0][2]
            self.env[v] = ('num', 1)
            if tgt[0] == 'index' and self.ev(tgt[1]) == ('tp',) and srcv[0] == 'index':
                key1 = self.ev(tgt[2])
                srcb = self.ev(srcv[1])
                usesv = srcv[2] == ('var', v) or v in str(srcv[2])
                if self.num(key1) and usesv:
                    if srcb[0] == 'packt':
                        self.effects.append(('callmulti', srcb[1], key1[1]))
                        self.effects.append(('settop', ('callmultiTop', key1[1])))
                        return
                    if srcb[0] == 'tr':
                        self.effects.append(('vararg-use', key1[1], 0))
                        return
        self.env[v] = ('unk', 'loopvar')
        self.depth += 1
        self.block(body)

    def forin(self, st):
        names, exprs, body = st[1], st[2], st[3]
        if len(exprs) == 1 and exprs[0][0] == 'call':
            f = self.ev(exprs[0][1])
            args = [self.ev(a) for a in exprs[0][2]]
            if f == ('fn', 'pairs'):
                src = args[0] if args else ('nil',)
                if src[0] == 'upvlist':
                    for i, (we, ez) in src[1]:
                        for n, val in zip(names, [('num', i), ('upvspec', we, ez)]):
                            self.env[n] = val
                        self.block(body)
                    return
        for n in names:
            self.env[n] = ('unk', 'forin')
        self.depth += 1
        self.block(body)

    def returnstat(self, vals):
        if not vals:
            self.effects.append(('return', 'none', None, None))
            return
        v = vals[0]
        if v[0] == 'range':
            if v[2] == 'top':
                self.effects.append(('return', 'varargs', v[1], None))
            else:
                self.effects.append(('return', 'range', v[1], v[2]))
        elif v[0] == 'reg':
            self.effects.append(('return', 'range', v[1], v[1]))
        elif v[0] == 'call':
            self.effects.append(('return', 'call', v, None))
        else:
            self.effects.append(('return', 'vals', vals, None))

    def assign(self, target, val):
        if target[0] == 'var':
            n = target[1]
            if n == 'tH':
                if self.num(val):
                    tgt = val[1]
                    if tgt != self.pc + 1:
                        self.effects.append(('jump', tgt))
                elif val[0] == 'unk':
                    pass
                self.env[n] = val if self.num(val) else ('num', self.pc + 1)
                return
            self.env[n] = val
            return
        if target[0] == 'index':
            base, key = self.ev(target[1]), self.ev(target[2])
            self.setindex(base, key, val)
            return
        if target[0] == 'massign':
            pass

    def setindex(self, base, key, val):
        b = base[0]
        if b == 'tp':
            if self.num(key):
                self.regknown[key[1]] = val
                if val[0] in ('num', 'str', 'bool', 'nil'):
                    self.effects.append(('setreg', key[1], val))
                else:
                    self.effects.append(('setreg', key[1], val))
            else:
                self.effects.append(('note', 'tP[symbolic]'))
        elif b == 'cvar':
            if self.num(key):
                self.cols[base[1]] = val[1] if self.num(val) else 0
        elif b == 'tr':
            if self.num(key):
                self.effects.append(('settr', key[1], val))
        elif b == 'top':
            self.effects.append(('settop', val))
        elif b == 'cells':
            self.effects.append(('celldef', key))
        elif b in ('env',):
            self.effects.append(('setglobal', key, val))
        else:
            if base[0] == 'getf' or base[0] in ('reg', 'upv', 'global'):
                self.effects.append(('setfield', base, key, val))

    def num(self, v):
        return isinstance(v, tuple) and v[0] == 'num'

    def ev(self, e):
        if not isinstance(e, tuple):
            return ('unk', str(e))
        k = e[0]
        if k in ('num', 'str', 'bool'):
            return (k, e[1])
        if k in ('nil', 'nilv'):
            return ('nil',)
        if k == 'vararg':
            return ('varargx',)
        if k == 'var':
            n = e[1]
            if n in self.env:
                return self.env[n]
            return ('nil',)
        if k == 'index':
            base = self.ev(e[1])
            key = self.ev(e[2])
            return self.getindex(base, key)
        if k == 'bin':
            a = self.ev(e[2])
            b = self.ev(e[3])
            return self.binop(e[1], a, b)
        if k == 'un':
            a = self.ev(e[2])
            if e[1] == 'not':
                t = truth(a)
                if t is None:
                    return ('un', 'not', a)
                return ('bool', not t)
            if e[1] == '-' and self.num(a):
                return ('num', -a[1])
            if e[1] == '#' and a[0] == 'str':
                return ('num', len(a[1]))
            return ('unk', 'unary')
        if k == 'call':
            return self.call(e[1], [self.ev(a) for a in e[2]])
        if k == 'massign':
            return ('unk', 'massign')
        if k == 'function':
            return ('unk', 'function')
        return ('unk', k)

    def binop(self, op, a, b):
        if op == 'and':
            if truth(a) is True:
                return b
            if truth(a) is False:
                return a
            return ('unk', 'and')
        if op == 'or':
            if truth(a) is True:
                return a
            if truth(a) is False:
                return b
            return ('unk', 'or')
        if self.num(a) and self.num(b):
            x, y = a[1], b[1]
            try:
                if op == '+':
                    return ('num', x + y)
                if op == '-':
                    return ('num', x - y)
                if op == '*':
                    return ('num', x * y)
                if op == '/':
                    return ('num', x / y)
                if op == '%':
                    return ('num', x % y)
                if op == '^':
                    return ('num', x ** y)
                if op == '..':
                    return ('str', str(x) + str(y))
            except Exception:
                return ('unk', 'arith')
            if op == '==':
                return ('bool', x == y)
            if op == '~=':
                return ('bool', x != y)
            if op == '<':
                return ('bool', x < y)
            if op == '<=':
                return ('bool', x <= y)
            if op == '>':
                return ('bool', x > y)
            if op == '>=':
                return ('bool', x >= y)
            return ('unk', op)
        if op in ('==', '~=', '<', '<=', '>', '>='):
            if a[0] == 'unk' or b[0] == 'unk':
                return ('unk', 'cmp')
            return ('cmp', op, a, b)
        if op == '..':
            return ('unk', 'concat')
        return ('bin', op, a, b)

    def getindex(self, base, key):
        b = base[0]
        if b == 'ih':
            if self.num(key):
                return ('cvar', key[1])
            return ('unk', 'ih')
        if b == 'cvar':
            if self.num(key) and key[1] == self.pc:
                return ('num', self.cols.get(base[1], 0))
            if self.num(key):
                nxt = key[1]
                if nxt > self.pc and nxt <= self.P['n']:
                    return ('num', self.P['ops'][nxt - 1] if base[1] == 4998 else
                            ((self.P.get('g3').cols.get(base[1]) or {}).get(nxt) or 0))
            return ('unk', 'col')
        if b == 'tp':
            if self.num(key):
                if key[1] in self.regknown:
                    return self.regknown[key[1]]
                return ('reg', key[1])
            return ('unk', 'tps')
        if b == 'uk':
            if self.num(key):
                tgt = self.P['uk'].get(self.pc)
                if key[1] == self.pc and tgt is not None:
                    return ('num', tgt)
            return ('unk', 'uk')
        if b == 'z':
            if self.num(key):
                return ('num', self.P.get('g3').m2130.get(key[1], 0))
            return ('unk', 'z')
        if b == 'l':
            if self.num(key):
                return ('num', self.P.get('g3').m1850.get(key[1], 0))
            return ('unk', 'l')
        if b == 'ek':
            if self.num(key):
                tok = self.sem.ek[key[1] - 1] if 0 < key[1] <= len(self.sem.ek) else 65535
                return ('num', tok)
            return ('unk', 'ek')
        if b == 'gb':
            if self.num(key):
                return ('proto', key[1])
            return ('unk', 'gb')
        if b == 'ts':
            if self.num(key):
                return ('upv', key[1])
            return ('unk', 'ts')
        if b == 'proto':
            if self.num(key) and key[1] == 4013:
                return ('upvlist', self.childupvals(base[1]))
            return ('unk', 'proto')
        if b == 'env':
            if key[0] == 'str':
                return ('global', key[1])
            return ('unk', 'env')
        if b == 'lib':
            if key[0] == 'str':
                return ('libfn', base[1], key[1])
            return ('unk', 'lib')
        if b == 'dxt':
            if self.num(key):
                return ('dxid', key[1])
            return ('unk', 'dx')
        if b == 'dnt':
            return ('unk', 'dN')
        if b == 'o8':
            if key[0] == 'dxid':
                n = key[1]
                nm = dxname.get(n)
                if nm == 'templates':
                    return ('tmpls',)
                if nm == 'env':
                    return ('env',)
                if nm == 'math':
                    return ('lib', 'math')
                if nm == 'string':
                    return ('lib', 'string')
                if nm == 'tamperstate':
                    return ('nil',)
                if nm in ('select', 'r', 'xor', 'floor', 'typeof', 'expand',
                          'pack', 'mulmod', 'pairs', 'getmetatable'):
                    return ('fn', nm)
                return ('o8fn', nm or n)
            if key[0] == 'str':
                return ('o8field', unesc(key[1]))
            return ('unk', 'o8')
        if b == 'tmpls':
            if self.num(key):
                return ('tmpl', key[1])
            return ('unk', 'tmpls')
        if b == 'top':
            return ('unk', 'top')
        if b == 'tr':
            if self.num(key):
                return ('trv', key[1])
            return ('unk', 'tr')
        if b == 'cells':
            if self.num(key):
                return ('cell', key[1])
            return ('unk', 'cells')
        if b == 'upvspec':
            if key[0] == 'str' and key[1] == 'EZ':
                return ('num', base[2])
            if key[0] == 'str' and key[1] == 'We':
                return ('bool', base[1])
            return ('unk', 'upvspec')
        if b in ('fn', 'libfn'):
            return ('unk', 'fieldoffn')
        if b == 'getf' or b in ('reg', 'upv', 'global', 'packt', 'callres', 'closure',
                                'newtbl', 'call', 'bin', 'un', 'stdlibcall', 'getf'):
            if key[0] == 'str' and key[1] == 'n':
                return ('unk', 'n')
            return ('getf', base, key)
        return ('getf', base, key)

    def childupvals(self, pid):
        child = None
        for pr in self.sem.vm.protos:
            if pr['pid'] == pid:
                child = pr
                break
        return [(bool(w), i) for w, i in (child['upvals'] if child else [])]

    def call(self, fexpr, args):
        f = self.ev(fexpr)
        if f[0] == 'fn':
            n = f[1]
            if n == 'r':
                tok = args[0] if args else ('nil',)
                if self.num(tok):
                    t = tok[1]
                    s = self.sem.strings.get(t)
                    if s is None:
                        return ('nil',)
                    return ('str', s)
                return ('nil',)
            if n == 'select':
                if len(args) >= 2:
                    return args[1]
                return ('nil',)
            if n == 'xor':
                if self.num(args[0]) and self.num(args[1]):
                    return ('num', (int(args[0][1]) ^ int(args[1][1])) & 0xFFFFFFFF)
                return ('unk', 'xor')
            if n == 'floor':
                if self.num(args[0]):
                    return ('num', int(args[0][1] // 1))
                return ('unk', 'floor')
            if n == 'mulmod':
                if self.num(args[0]) and self.num(args[1]):
                    return ('num', (args[0][1] * args[1][1]) % 4294967296)
                return ('unk', 'mulmod')
            if n == 'typeof':
                if args and args[0][0] in ('fn', 'libfn'):
                    return ('str', 'function')
                if args and args[0][0] in ('num',):
                    return ('str', 'number')
                if args and args[0][0] == 'str':
                    return ('str', 'string')
                return ('unk', 'type')
            if n == 'expand':
                a = args[1] if len(args) > 1 else ('num', 0)
                b = args[2] if len(args) > 2 else ('num', 0)
                if self.num(a) and self.num(b):
                    return ('range', a[1], b[1])
                if self.num(a):
                    return ('range', a[1], 'top')
                return ('unk', 'expand')
            if n == 'pack':
                return ('packt', args[1] if len(args) > 1 else ('nil',))
            return ('unk', 'fn ' + n)
        if f[0] == 'o8fn':
            n = f[1]
            if n == 'mkclosure' and args and args[0][0] == 'proto':
                return ('closure', args[0][1])
            return ('unk', 'o8call')
        if f[0] == 'libfn':
            lib, name = f[1], f[2]
            if lib == 'math' and name == 'floor' and self.num(args[0]):
                return ('num', int(args[0][1]))
            return ('stdlibcall', lib, name, args)
        if f[0] == 'o8field':
            return ('unk', 'o8field call')
        if f[0] in ('unk', 'nil'):
            return ('unk', 'call?')
        if f[0] == 'getf' and f[1][0] == 'unk':
            return ('unk', 'call')
        return ('call', f, args, None)



def istypetest(cond):
    if not isinstance(cond, tuple):
        return False
    if cond[0] == 'un' and len(cond) > 2:
        return istypetest(cond[2])
    if cond[0] != 'cmp' or len(cond) < 4:
        return False
    for a, b in ((cond[2], cond[3]), (cond[3], cond[2])):
        if isinstance(a, tuple) and a[0] == 'unk' and a[1:2] == ('type',) \
                and isinstance(b, tuple) and b[0] == 'str':
            return True
    def hasunk(v):
        if not isinstance(v, tuple):
            return False
        if v[0] == 'unk' and v[1:2] == ('type',):
            return True
        return any(hasunk(x) for x in v[1:] if isinstance(x, tuple))
    return hasunk(cond)


def truth(v):
    if v is None:
        return None
    k = v[0]
    if k == 'num':
        return v[1] != 0
    if k == 'str':
        return v[1] != ''
    if k == 'bool':
        return v[1]
    if k == 'nil':
        return False
    if k == 'unk':
        return None
    return True


def hashy(s):
    return 0


def g3classify(vm):
    sem = g3sem(vm)
    kinds = {}
    for op in vm.handlers:
        if op in sem.junkops:
            kinds[op] = 'JUNK'
            continue
        body = sem.handlers[op]
        if 'tH=RT[tH]' in body and 'tP[Rq[tH]]' in body:
            kinds[op] = 'TEST'
        elif re.search(r'return Qo\(tP,', body):
            kinds[op] = 'RETURN'
        elif 'mkclosure' in body or ('gb[' in body and 'o8[dx[54546]]' in body):
            kinds[op] = 'CLOSURE'
        elif 'o8[dx[58054]]' in body or re.search(r'R\d\(\w+\(tP,', body):
            kinds[op] = 'CALL'
        elif 'tr[' in body or 'tr=' in body:
            kinds[op] = 'VARARG'
        elif 'o8[dx[6527]]' in body:
            kinds[op] = 'NEWTABLE'
        elif 'o8[dx[12777]]' in body:
            kinds[op] = 'GLOBAL'
        elif 'eK[' in body:
            kinds[op] = 'CONST'
        elif 'RT[tH]' in body:
            kinds[op] = 'JMP'
        elif 'tP[' in body:
            kinds[op] = 'REGOP'
        else:
            kinds[op] = 'OTHER'
    return kinds
