from __future__ import annotations
import math
import re
from .nb import builtinnames, nbclean, nberror, nbparse

class lsym:
    __slots__ = ('t', 'a')

    def __init__(self, t, *a):
        self.t, self.a = (t, a)

    def __repr__(self):
        return '%s%r' % (self.t, self.a)

    def __eq__(self, other):
        return isinstance(other, lsym) and self.t == other.t and (self.a == other.a)

    def __hash__(self):
        return hash((self.t, self.a))

def S(t, *a):
    return lsym(t, *a)

def symhas(sym, t):
    if not isinstance(sym, lsym):
        return False
    if sym.t == t:
        return True
    for x in sym.a:
        if isinstance(x, lsym) and symhas(x, t):
            return True
        if isinstance(x, tuple):
            for y in x:
                if isinstance(y, lsym) and symhas(y, t):
                    return True
    return False

def hasnilcmp(sym):
    if not isinstance(sym, lsym):
        return False
    if sym.t == 'cmp' and sym.a[0] in ('==', '~='):
        for x in (sym.a[1], sym.a[2]):
            if isinstance(x, lsym) and x.t == 'const' and (x.a[0] is None):
                return True
    if sym.t in ('and', 'or'):
        for x in sym.a:
            if hasnilcmp(x):
                return True
    return False
typenames = {'table', 'function', 'string', 'number', 'boolean', 'thread', 'userdata', 'nil'}

def hassentinelcmp(sym):
    if not isinstance(sym, lsym):
        return False
    if sym.t == 'cmp' and sym.a[0] in ('==', '~='):
        l, r = (sym.a[1], sym.a[2])
        for a, b in ((l, r), (r, l)):
            if isinstance(a, lsym) and a.t == 'const' and isinstance(a.a[0], str) and (a.a[0] in typenames) and (not (isinstance(b, lsym) and b.t == 'type')):
                return True
    if sym.t in ('and', 'or'):
        for x in sym.a:
            if hassentinelcmp(x):
                return True
    return False

def hastypecmp(sym):
    if not isinstance(sym, lsym):
        return False
    if sym.t == 'cmp':
        l, r = (sym.a[1], sym.a[2])
        for a, b in ((l, r), (r, l)):
            bv = b.a[0] if isinstance(b, lsym) and b.t == 'const' else b
            if isinstance(a, lsym) and a.t == 'type' and isinstance(bv, str) and (bv != 'function'):
                return True
    for x in sym.a:
        if isinstance(x, lsym) and hastypecmp(x):
            return True
        if isinstance(x, tuple):
            for y in x:
                if isinstance(y, lsym) and hastypecmp(y):
                    return True
    return False

class stop2(Exception):

    def __init__(self, value):
        self.value = value

class encstr:
    __slots__ = ('idx',)

    def __init__(self, idx):
        self.idx = idx

class pack3:

    def __init__(self, call, fixed=None):
        self.call, self.fixed = (call, fixed)

class regrange:

    def __init__(self, a, b):
        self.a, self.b = (a, b)

class tablit:
    __slots__ = ('vals', 'base', 'items')

    def __init__(self, vals, base=None):
        self.vals = vals
        self.base = base
        self.items = {}

    def __bool__(self):
        return True

class regs2:
    pass

class upvals:
    pass

class envtab:
    pass

class opstab:
    pass

class uktab:
    pass

class uetab:
    pass

class uftab:
    pass

class ufxtab:
    pass

class maptab:
    pass

class pooltab:
    pass

class protostab:
    pass

class keylisttab:
    pass

class constdec:
    pass

class unpackregs:
    pass

class packstub:
    pass

class floorstub:
    pass

class typestub:
    pass

class nextstub:
    pass

class unpack3stub:
    pass

class mathfn:

    def __init__(self, name):
        self.name = name

class mathlib:

    def getfn(self, name):
        if not isinstance(name, str):
            raise nberror('math[?]')
        return mathfn(name)

class coltab:

    def __init__(self, n, dec):
        self.n, self.dec = (n, dec)

    def __getitem__(self, pc):
        cx = self.dec.curctx
        if cx is not None and pc == cx.pc:
            return cx.cols.get(self.n, 0)
        return self.dec.P['regs'][self.n].get(pc) or 0

class colidtab:

    def __init__(self, dec):
        self.dec = dec
        self.map = {cid: n for n, cid in enumerate(dec.vm.colids or [])}

    def __getitem__(self, cid):
        if cid in self.map:
            return coltab(self.map[cid], self.dec)
        raise nberror('ColIdTab[%s]' % (cid,))

class falsystub:

    def __bool__(self):
        return False

    def __call__(self, *a, **k):
        return falsystub()

    def __getitem__(self, k):
        return falsystub()

    def __setitem__(self, k, v):
        pass

    def __repr__(self):
        return '<falsy>'

class stubtab:
    pack2 = {60120, 42298}
    dec2 = {34681, 19563, 62001, 65369}
    unpack3 = {12342, 63097}

    def __init__(self, dec):
        self.dec = dec

    def getstub(self, k):
        if k in self.pack2:
            return packstub()
        if k in self.dec2:
            return constdec()
        if k in self.unpack3:
            return unpack3stub()
        if k in (17816, 41886):
            return floorstub()
        if k in (29648, 996):
            return nextstub()
        if k in (24223, 46430):
            return keylisttab()
        self.dec.noteunknownstub(k)
        return falsystub()

def xor(a, b):
    if isinstance(a, bool) or isinstance(b, bool):
        raise nberror('xor on bool')
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return int(a) ^ int(b)
    raise nberror('xor(%r,%r)' % (a, b))

class ctx2:

    def __init__(self, dec, pc):
        self.dec = dec
        self.pc = pc
        self.cols = {c: dec.P['regs'][c].get(pc) or 0 for c in range(8)}
        self.effects = []
        self.newpc = None
        self.ret = None

    def eff(self, *e):
        self.effects.append(e)

class irdecoder:

    def __init__(self, sem, P):
        self.sem = sem
        self.vm = sem.vm
        self.P = P
        self.uk = P.get('uk', {})
        self.ue = P.get('ue', {})
        self.uf = P.get('uf', {})
        self.ufx = P.get('ufx', {})
        self.unknownstubs = set()
        self.curctx = None
        self.g2 = None

    def noteunknownstub(self, k):
        self.unknownstubs.add(k)

    def decode(self, i):
        op = self.P['ops'][i - 1]
        o = self.sem.ops.get(op)
        if o is None:
            return {'i': i, 'op': op, 'kind': 'NOHANDLER', 'effects': [], 'newpc': None}
        kind = o['kind']
        fn = special.get(kind)
        if fn is not None:
            try:
                return fn(self, i, o)
            except Exception as e:
                return {'i': i, 'op': op, 'kind': kind, 'error': 'spl: %s: %s' % (type(e).__name__, e), 'effects': [], 'newpc': None}
        d = self.decodegeneric(i, op, kind, o)
        if not d.get('error'):
            return d
        err = d['error']
        for rx, tfn in nbtemplates:
            if rx.search(o['nb']):
                try:
                    return tfn(self, i, o)
                except Exception as e:
                    err = 'tpl: %s: %s' % (type(e).__name__, e)
        d['error'] = err
        return d

    def decodegeneric(self, i, op, kind, o):
        nb = nbclean(o['nb'])
        ctx = ctx2(self, i)
        self.curctx = ctx
        try:
            self.execblock(nbparse(nb), {}, ctx)
        except stop2 as st:
            ctx.ret = st.value
        except nberror as e:
            self.curctx = None
            return {'i': i, 'op': op, 'kind': kind, 'error': str(e), 'effects': ctx.effects, 'newpc': ctx.newpc}
        self.curctx = None
        effs = list(ctx.effects)
        if ctx.ret is not None:
            effs.append(self.reteffect(ctx.ret))
        return {'i': i, 'op': op, 'kind': kind, 'effects': effs, 'newpc': ctx.newpc, 'ret': ctx.ret}

    def reteffect(self, ret):
        if ret is None:
            return ('return',)
        vals = ret
        if len(vals) == 1 and isinstance(vals[0], regrange):
            rr = vals[0]
            if isinstance(rr.a, int) and isinstance(rr.b, int):
                return ('return', rr.a, rr.b)
            if isinstance(rr.a, int):
                return ('returnm', rr.a)
        if len(vals) == 1 and isinstance(vals[0], lsym):
            return ('returnvals', (vals[0],))
        return ('returnraw', tuple((self.symify(v) for v in vals)))

    def execblock(self, stmts, env, ctx):
        for st in stmts:
            self.execstmt(st, env, ctx)

    def execstmt(self, st, env, ctx):
        k = st[0]
        if k == 'local':
            _, names, exprs = st
            if len(exprs) == 1 and exprs[0][0] == 'call' and (len(names) > 1):
                fv = self.eval(exprs[0], env, ctx)
                if isinstance(fv, lsym) and fv.t == 'call':
                    for idx, n in enumerate(names):
                        env[n] = S('callres', fv, idx)
                    return
                vals = [fv] + [None] * (len(names) - 1)
            else:
                vals = [self.eval(e, env, ctx) for e in exprs] if exprs else [None] * len(names)
                if len(vals) < len(names):
                    vals = vals + [None] * (len(names) - len(vals))
            for n, v in zip(names, vals):
                env[n] = v
            return
        if k == 'assign':
            _, tgts, exprs = st
            if len(exprs) == 1 and exprs[0][0] == 'call' and (len(tgts) > 1) and all((t[0] == 'name' for t in tgts)):
                fv = self.eval(exprs[0], env, ctx)
                if isinstance(fv, lsym) and fv.t == 'call':
                    for idx, n in enumerate(tgts):
                        env[n[1]] = S('callres', fv, idx)
                    return
                vals = [fv] + [None] * (len(tgts) - 1)
            else:
                vals = [self.eval(e, env, ctx) for e in exprs]
                if len(tgts) > len(vals):
                    vals = vals + [None] * (len(tgts) - len(vals))
            for tgt, v in zip(tgts, vals):
                self.assign(tgt, v, env, ctx)
            return
        if k == 'callstat':
            v = self.eval(st[1], env, ctx)
            if isinstance(v, lsym) and v.t == 'call':
                ctx.eff('expr', v)
            return
        if k == 'if':
            _, branches, els = st
            for cond, blk in branches:
                c = self.condbranch(cond, blk, env, ctx)
                if c == 'JUMPED':
                    return
                if c is True:
                    self.execblock(blk, env, ctx)
                    return
                if c is False:
                    continue
                raise nberror('unresolved branch: %r' % (cond,))
            if els is not None:
                self.execblock(els, env, ctx)
            return
        if k == 'while':
            _, cond, blk = st
            while True:
                c = self.condbranch(cond, blk, env, ctx)
                if c is False:
                    return
                if c is not True:
                    raise nberror('unresolved while cond %r' % (cond,))
                self.execblock(blk, env, ctx)
            return
        if k == 'fornum':
            return self.execfornum(st, env, ctx)
        if k in ('fornin', 'forin'):
            return self.execforin(st, env, ctx)
        if k == 'do':
            self.execblock(st[1], env, ctx)
            return
        if k == 'return':
            v = [self.eval(e, env, ctx) for e in st[1]] if st[1] else None
            raise stop2(v)
        if k == 'break':
            raise nberror('break reached')
        raise nberror('stmt %r' % (st,))

    def execforin(self, st, env, ctx):
        _, names, e, body = st
        if isinstance(e, tuple) and len(e) == 1:
            e = e[0]
        if e[0] != 'call':
            raise nberror('forin expr %r' % (e,))
        call = e
        if not call[2]:
            raise nberror('forin call no args')
        try:
            srcv = self.eval(call[2][0], env, ctx)
        except nberror:
            raise
        if isinstance(srcv, list):
            seq = [(i + 1, v) for i, v in enumerate(srcv)]
        elif isinstance(srcv, tablit) and srcv.base is None:
            seq = [(i + 1, v) for i, v in enumerate(srcv.vals)]
        else:
            raise nberror('fornin over %r' % (srcv,))
        for idx, item in seq:
            env[names[0]] = idx
            if len(names) > 1:
                env[names[1]] = item
            self.execblock(body, env, ctx)

    def execfornum(self, st, env, ctx):
        _, var, a, b, c, body = st
        av = self.eval(a, env, ctx)
        bv = self.eval(b, env, ctx)
        cv = self.eval(c, env, ctx)
        if not all((isinstance(x, int) for x in (av, bv, cv))):
            return self.trymultretloop(var, av, bv, cv, body, env, ctx)
        if av == 1 and len(body) == 1 and (body[0][0] == 'assign'):
            asg = body[0]
            if len(asg[1]) == 1 and len(asg[2]) == 1 and (asg[1][0][0] == 'index') and (asg[2][0][0] == 'index') and (asg[2][0][1] == ('name', 'R')):
                tgt, rhs = (asg[1][0], asg[2][0])
                if tgt[1][0] == 'name' and tgt[2] == ('name', var):
                    based = self.indexplusvar(rhs[2], var)
                    if based is not None:
                        basex, kk = based
                        bval = self.eval(basex, env, ctx)
                        if isinstance(bval, int):
                            env[tgt[1][1]] = tablit([], base=bval + 1 + kk)
                            return
        if av > bv:
            return
        step = cv if cv > 0 else 1
        for kk in range(av, bv + 1, step):
            env[var] = kk
            self.execblock(body, env, ctx)

    def trymultretloop(self, var, av, bv, cv, body, env, ctx):
        if av != 1 or len(body) != 1 or body[0][0] != 'assign':
            raise nberror('symbolic fornum %r' % (body,))
        tgt, rhs = (body[0][1][0], body[0][2][0])
        if rhs[0] != 'index' or rhs[2] != ('name', var):
            raise nberror('symbolic fornum rhs %r' % (rhs,))
        pack = self.eval(rhs[1], env, ctx)
        if not isinstance(pack, pack3):
            raise nberror('symbolic fornum pack %r' % (pack,))
        if tgt[0] != 'index' or tgt[1] != ('name', 'R'):
            raise nberror('symbolic fornum tgt %r' % (tgt,))
        based = self.indexplusvar(tgt[2], var)
        if based is None:
            raise nberror('symbolic fornum tgt idx %r' % (tgt[2],))
        basex, k = based
        v = self.eval(basex, env, ctx)
        if not isinstance(v, int):
            raise nberror('symbolic fornum base %r' % (v,))
        base = v + 1 + k
        if pack.fixed is not None:
            for off in range(pack.fixed):
                ctx.eff('set', S('reg', base + off), S('callres', pack.call, off))
        else:
            ctx.eff('setm', base, pack.call)
        return

    def indexplusvar(self, idxexpr, var):

        def split(e):
            if e == ('name', var):
                return (None, 1, 0)
            if e[0] == 'num':
                return (None, 0, e[1])
            if e[0] == 'bin' and e[1] == '+':
                l, r = (split(e[2]), split(e[3]))
                if l and r:
                    if l[0] is None and r[0] is None:
                        return None
                    if l[0] is None:
                        return (r[0], r[1] + l[1], r[2] + l[2])
                    if r[0] is None:
                        return (l[0], l[1] + r[1], l[2] + r[2])
                return None
            if e[0] == 'bin' and e[1] == '-':
                l, r = (split(e[2]), split(e[3]))
                if l and r and (r[0] is None) and (r[1] == 0):
                    return (l[0], l[1], l[2] - r[2])
                return None
            if e[0] in ('name', 'call', 'index', 'at'):
                return (e, 0, 0)
            return None
        s = split(idxexpr)
        if not s or s[1] != 1:
            return None
        A, _, k = s
        return (A, k)

    def assign(self, tgt, val, env, ctx):
        if tgt[0] == 'name':
            n = tgt[1]
            if n == 'PC':
                if isinstance(val, int):
                    ctx.newpc = val
                    return
                if val is None:
                    ctx.newpc = ctx.pc + 1
                    return
                raise nberror('PC=%r' % (val,))
            if n in ('TOP', 'MT'):
                return
            if n in ignoredwrites:
                return
            if n in env:
                env[n] = val
                return
            if n in builtinnames:
                raise nberror('assign to builtin global %r' % n)
            env[n] = val
            return
        if tgt[0] == 'at':
            if isinstance(val, int):
                ctx.cols[tgt[1]] = val
                return
            raise nberror('@%d=%r' % (tgt[1], val))
        if tgt[0] == 'index' and tgt[1][0] == 'at':
            N = tgt[1][1]
            if isinstance(val, int):
                ctx.cols[N] = val
                return
            raise nberror('@%d[PC]=%r' % (N, val))
        if tgt[0] == 'index':
            self.assignindex(tgt[1], tgt[2], val, env, ctx)
            return
        raise nberror('assign target %r' % (tgt,))

    def assignindex(self, obj, key, val, env, ctx):
        ov = self.eval(obj, env, ctx)
        kv = self.eval(key, env, ctx)
        if isinstance(ov, regs2):
            n = self.toint(kv)
            ctx.eff('set', S('reg', n), self.symify(val))
            return
        if isinstance(ov, upvals):
            n = self.toint(kv)
            ctx.eff('set', S('upv', n - 1), self.symify(val))
            return
        if isinstance(ov, envtab):
            if not (isinstance(kv, lsym) and kv.t == 'const' and isinstance(kv.a[0], str)):
                raise nberror('ENV[%r]=...' % (kv,))
            ctx.eff('set', S('glob', kv.a[0]), self.symify(val))
            return
        if isinstance(ov, coltab):
            pc = self.toint(kv)
            if ctx.pc == pc and isinstance(val, int):
                ctx.cols[ov.n] = val
                return
            raise nberror('ColTab write pc=%d' % (pc,))
        if isinstance(ov, falsystub):
            return
        if isinstance(ov, tablit):
            kk = kv
            if isinstance(kv, lsym) and kv.t == 'const':
                kk = kv.a[0]
            if isinstance(kk, (int, str)) and (not isinstance(kk, bool)):
                vv = val
                if isinstance(val, lsym) and val.t == 'const':
                    vv = val.a[0]
                ov.items[kk] = vv
            return
        if isinstance(ov, lsym) and ov.t == 'reg':
            ctx.eff('set', S('index', ov, self.keyval(kv)), self.symify(val))
            return
        if isinstance(ov, lsym) and ov.t == 'upv':
            ctx.eff('set', S('upvindex', ov, self.keyval(kv)), self.symify(val))
            return
        raise nberror('index assign obj=%r key=%r' % (ov, kv))

    def keyval(self, kv):
        if isinstance(kv, lsym):
            return kv
        if isinstance(kv, (int, float)):
            return S('const', int(kv) if isinstance(kv, float) and kv.is_integer() else kv)
        if isinstance(kv, str):
            return S('const', kv)
        raise nberror('key %r' % (kv,))

    def eval(self, e, env, ctx):
        k = e[0]
        if k == 'num':
            return e[1]
        if k == 'str':
            return e[1]
        if k == 'true':
            return True
        if k == 'false':
            return False
        if k == 'nil':
            return None
        if k == 'tabcon':
            vals = [self.eval(x, env, ctx) for x in e[1]]
            return tablit(vals)
        if k == 'table':
            return tablit([])
        if k == 'at':
            return ctx.cols.get(e[1], 0)
        if k == 'name':
            return self.lookup(e[1], env, ctx)
        if k == 'index':
            return self.evalindex(e, env, ctx)
        if k == 'call':
            return self.evalcall(e, env, ctx)
        if k == 'un':
            return self.evalun(e, env, ctx)
        if k == 'bin':
            return self.evalbin(e, env, ctx)
        if k == 'and':
            l = self.eval(e[1], env, ctx)
            if l is None or l is False:
                return l
            if isinstance(l, lsym):
                return S('and', l, self.eval(e[2], env, ctx))
            return self.eval(e[2], env, ctx)
        if k == 'or':
            l = self.eval(e[1], env, ctx)
            if l is not None and l is not False:
                return l
            if isinstance(l, lsym):
                return S('or', l, self.eval(e[2], env, ctx))
            return self.eval(e[2], env, ctx)
        raise nberror('eval %r' % (e,))

    def evalun(self, e, env, ctx):
        _, op, x = e
        v = self.eval(x, env, ctx)
        if op == '-':
            if isinstance(v, (int, float)) and (not isinstance(v, bool)):
                return -v
            if isinstance(v, lsym):
                return S('neg', v)
            raise nberror('neg %r' % (v,))
        if op == '#':
            if isinstance(v, pack3):
                if v.fixed is not None:
                    return v.fixed
                return S('packn', v)
            if isinstance(v, str):
                return len(v)
            if isinstance(v, tablit):
                return len(v.vals)
            if isinstance(v, list):
                return len(v)
            if isinstance(v, lsym):
                return S('len', v)
            raise nberror('len %r' % (v,))
        if op == 'not':
            if isinstance(v, lsym):
                return S('not', v)
            return not (v is not None and v is not False)
        raise nberror('un %r' % (e,))

    def evalbin(self, e, env, ctx):
        _, op, le, re2 = e
        l = self.eval(le, env, ctx)
        r = self.eval(re2, env, ctx)
        if op == '..':
            if isinstance(l, str) and isinstance(r, str):
                return l + r
            raise nberror('concat %r %r' % (l, r))
        if isinstance(l, lsym) or isinstance(r, lsym):
            l = l if isinstance(l, lsym) else S('const', l)
            r = r if isinstance(r, lsym) else S('const', r)
            if op in ('+', '-', '*', '/', '%', '^'):
                return S('arith', op, l, r)
            if op in ('==', '~=', '<', '>', '<=', '>='):
                return S('cmp', op, l, r)
            raise nberror('symbolic bin %s %r %r' % (op, l, r))
        try:
            if op == '+':
                return l + r
            if op == '-':
                return l - r
            if op == '*':
                return l * r
            if op == '/':
                return l / r if r != 0 else 0.0
            if op == '%':
                if r == 0:
                    return 0.0 if isinstance(l, float) else 0
                return math.fmod(l, r)
            if op == '^':
                return l ** r
            if op == '==':
                return l == r
            if op == '~=':
                return l != r
            if op == '<':
                return l < r
            if op == '>':
                return l > r
            if op == '<=':
                return l <= r
            if op == '>=':
                return l >= r
        except TypeError:
            raise nberror('bin %s %r %r' % (op, l, r))
        raise nberror('bin %s' % op)

    def lookup(self, n, env, ctx):
        if n in env:
            return env[n]
        if n == 'PC':
            return ctx.pc
        if n == 'XOR':
            return xor
        g = self.globals(ctx)
        if n in g:
            return g[n]
        ctx.unknownreads = getattr(ctx, 'unknownreads', set())
        ctx.unknownreads.add(n)
        return None

    def globals(self, ctx):
        if self.g2 is None:
            self.g2 = self.makeglobals()
        return self.g2

    def makeglobals(self):
        return {'R': regs2(), 'Mp': regs2(), 'TOP': S('top'), 'MT': S('top'), 'ENV': envtab(), 'UPV': upvals(), 'Mj': upvals(), 'MAP': maptab(), 'tZ': maptab(), 'HS': maptab(), 'POOL': pooltab(), 'KEY': 'KEY', 'DEC': constdec(), 'UK': uktab(), 'Ue': uetab(), 'UF': uftab(), 'UFX': ufxtab(), 'UY': self.P.get('uy', 0), 'UR': self.P.get('ur', 0), 'PROTOS': protostab(), 'MZ': opstab(), 'Jq': colidtab(self), 'XH': colidtab(self), 'Mi': coltab(1, self), 'Md': coltab(2, self), 'MY': coltab(0, self), 'n3': unpackregs(), 'gA': unpackregs(), 'q7': unpackregs(), 'O0': unpackregs(), 'zj': typestub(), 'Iv': typestub(), 'type': typestub(), 'zU': 'function', 'Ia': 'function', 'zM': 'table', 'IM': 'table', 'zH': 'number', 'Ix': 'number', 'zx': 'string', 'Ik': 'string', 'zr': 'boolean', 'zt': False, 'Im': False, 'MI': False, 'QZ': False, 'MB': {}, 'bO': {}, 'MD': {}, 'Q6': {}, 'CELLS': {}, 'MJ': S('vararg'), 'Q9': S('vararg'), 'Mx': S('args'), 'Q7': S('args'), 'MH': 0, 'Mr': tablit([]), 'Q0s': None, 'Q0': tablit([]), 'zD': 'n', 'IE': 'n', 'nV': mathlib(), 'Og': mathlib(), 'nE': mathlib(), 'OJ': mathlib(), 'zm': mathlib(), 'n8': stublib(self), 'O9': stublib(self), 'zk': keyid(), 'IF': keyid(), 'IZ': keyid(), 'zV': keyid()}

    def evalindex(self, e, env, ctx):
        _, oe, ke = e
        if oe[0] == 'at':
            N = oe[1]
            pcx = self.toint(self.eval(ke, env, ctx))
            if pcx == ctx.pc:
                return ctx.cols.get(N, 0)
            return self.P['regs'][N].get(pcx) or 0
        ov = self.eval(oe, env, ctx)
        kv = self.eval(ke, env, ctx)
        if isinstance(ov, regs2):
            return S('reg', self.toint(kv))
        if isinstance(ov, upvals):
            return S('upv', self.toint(kv) - 1)
        if isinstance(ov, envtab):
            if isinstance(kv, str):
                return S('glob', kv)
            if isinstance(kv, lsym) and kv.t == 'const':
                return S('glob', kv.a[0])
            raise nberror('ENV[%r]' % (kv,))
        if isinstance(ov, opstab):
            n = self.toint(kv)
            if 1 <= n <= len(self.P['ops']):
                return self.P['ops'][n - 1]
            return 0
        if isinstance(ov, uktab):
            return self.uk.get(self.toint(kv))
        if isinstance(ov, ufxtab):
            return self.ufx.get(self.toint(kv))
        if isinstance(ov, uftab):
            return self.uf.get(self.toint(kv))
        if isinstance(ov, uetab):
            return self.ue.get(self.toint(kv))
        if isinstance(ov, maptab):
            return encstr(self.toint(kv))
        if isinstance(ov, pooltab):
            n = self.toint(kv)
            v = self.sem.doubles.get(n)
            if v is None:
                self.notemissingdouble(n)
            return v
        if isinstance(ov, protostab):
            return S('proto', self.toint(kv))
        if isinstance(ov, keylisttab):
            n = self.toint(kv)
            return self.sem.keylists.get(n)
        if isinstance(ov, mathlib):
            return ov.getfn(kv if isinstance(kv, str) else None)
        if isinstance(ov, (coltab, colidtab)):
            return ov[self.toint(kv)]
        if isinstance(ov, keyid):
            return ov[kv]
        if isinstance(ov, stublib):
            return ov.getstub(self.toint(kv)) if isinstance(kv, int) else ov.getstubname(kv)
        if isinstance(ov, pack3):
            if isinstance(kv, str) and kv == 'n':
                return vfixedorpackn(ov)
            if isinstance(kv, int):
                return S('callres', ov.call, kv - 1)
            raise nberror('PACK[%r]' % (kv,))
        if isinstance(ov, tablit):
            if isinstance(kv, int):
                if kv in ov.items:
                    return ov.items[kv]
                if 1 <= kv <= len(ov.vals):
                    return ov.vals[kv - 1]
                if isinstance(ov.base, int):
                    return S('reg', ov.base + kv - 1)
                return None
            if isinstance(kv, str):
                if kv in ov.items:
                    return ov.items[kv]
                return None
            raise nberror('TabLit[%r]' % (kv,))
        if isinstance(ov, str):
            raise nberror('string index %r[%r]' % (ov, kv))
        if isinstance(ov, list):
            n = self.toint(kv)
            if 1 <= n <= len(ov):
                return ov[n - 1]
            return None
        if isinstance(ov, falsystub):
            return falsystub()
        if isinstance(ov, lsym):
            kk = self.keyval(kv)
            if ov.t in ('reg', 'upv', 'glob', 'const', 'index'):
                return S('index', ov, kk)
            if ov.t == 'vararg':
                if isinstance(kv, str) and kv == 'n':
                    return S('vararg_n')
                raise nberror('vararg index %r' % (kv,))
            raise nberror('index into %r' % (ov,))
        if isinstance(ov, (bool, int, float)) or ov is None:
            raise nberror('index into %r' % (ov,))
        raise nberror('index obj %r' % (ov,))

    def iscolwrite(self, tgt):
        return tgt[0] == 'index' and tgt[1][0] == 'at' and (tgt[2] == ('name', 'PC'))

    def evalcall(self, e, env, ctx):
        _, fe, args = e
        fv = self.eval(fe, env, ctx)
        if isinstance(fv, constdec):
            if len(args) == 2:
                m = self.eval(args[0], env, ctx)
                if isinstance(m, encstr):
                    v = self.resolvemap(m.idx)
                    return S('const', v)
                if isinstance(m, int):
                    v = self.resolvemap(m)
                    return S('const', v)
                raise nberror('DEC(%r)' % (m,))
            if len(args) == 1:
                m = self.eval(args[0], env, ctx)
                if isinstance(m, encstr):
                    v = self.resolvemap(m.idx)
                    return S('const', v) if v is not None else S('constidx', m.idx)
            raise nberror('DEC args %r' % (args,))
        if isinstance(fv, unpackregs):
            if len(args) == 3:
                src = self.eval(args[0], env, ctx)
                a = self.eval(args[1], env, ctx)
                b = self.eval(args[2], env, ctx)
                if isinstance(src, tablit) and isinstance(src.base, int):
                    if isinstance(a, int) and isinstance(b, int):
                        return regrange(src.base + a - 1, src.base + b - 1)
                    raise nberror('slice range %r %r' % (a, b))
                if isinstance(src, tablit) and src.base is None:
                    if isinstance(a, int) and isinstance(b, int):
                        vals = src.vals[a - 1:b]
                        vals = [v for v in vals if v is not None]
                        return tuple(vals)
                    raise nberror('scratch slice %r %r' % (a, b))
                return regrange(a, b)
            raise nberror('unpack-regs args %r' % (args,))
        if isinstance(fv, packstub):
            if len(args) == 2:
                fixed = self.eval(args[0], env, ctx)
                callexpr = self.eval(args[1], env, ctx)
                if isinstance(callexpr, lsym) and callexpr.t == 'call':
                    return pack3(callexpr, fixed if isinstance(fixed, int) else None)
                if isinstance(callexpr, lsym) and callexpr.t in ('index', 'reg', 'glob', 'upv'):
                    return pack3(callexpr, fixed if isinstance(fixed, int) else None)
                raise nberror('pack of %r' % (callexpr,))
            raise nberror('pack args %r' % (args,))
        if isinstance(fv, floorstub):
            v = self.eval(args[0], env, ctx)
            if isinstance(v, (int, float)) and (not isinstance(v, bool)):
                return int(v - math.fmod(v, 1))
            if isinstance(v, lsym):
                return v
            raise nberror('floor(%r)' % (v,))
        if isinstance(fv, typestub):
            v = self.eval(args[0], env, ctx)
            if isinstance(v, bool):
                return 'boolean'
            if isinstance(v, (int, float)):
                return 'number'
            if isinstance(v, str):
                return 'string'
            if v is None:
                return 'nil'
            if isinstance(v, lsym):
                return S('type', v)
            if isinstance(v, (regs2, envtab, upvals, maptab, pooltab, opstab, uktab, ufxtab, uftab, uetab, protostab, mathlib, keylisttab, coltab, colidtab, tablit, dict)):
                return 'table'
            if isinstance(v, (constdec, unpackregs, packstub, floorstub, typestub, nextstub, unpack3stub, mathfn)) or callable(v):
                return 'function'
            if isinstance(v, falsystub):
                return 'nil'
            raise nberror('type(%r)' % (v,))
        if isinstance(fv, mathfn):
            vals = [self.eval(a, env, ctx) for a in args]
            if all((isinstance(x, (int, float)) and (not isinstance(x, bool)) for x in vals)):
                try:
                    if fv.name == 'fmod':
                        return math.fmod(vals[0], vals[1])
                    if fv.name == 'pow':
                        return vals[0] ** vals[1]
                    if fv.name in ('min', 'max'):
                        return (min if fv.name == 'min' else max)(vals)
                    if fv.name == 'abs':
                        return abs(vals[0])
                    if fv.name == 'floor':
                        return int(vals[0] - math.fmod(vals[0], 1))
                    if fv.name == 'ceil':
                        return int(-(-vals[0] // 1)) if isinstance(vals[0], int) else math.ceil(vals[0])
                    if fv.name == 'sqrt':
                        return math.sqrt(vals[0])
                    return getattr(math, {'sin': 'sin', 'cos': 'cos', 'tan': 'tan', 'exp': 'exp', 'log': 'log', 'deg': 'degrees', 'rad': 'radians', 'asin': 'asin', 'acos': 'acos', 'atan': 'atan', 'atan2': 'atan2', 'ldexp': 'ldexp', 'modf': 'modf'}.get(fv.name, fv.name))(*vals)
                except (AttributeError, ValueError, OverflowError):
                    raise nberror('math.%s(%r)' % (fv.name, vals))
            if fv.name in ('insert', 'remove', 'concat', 'unpack', 'pack', 'select', 'byte', 'char', 'len', 'sub', 'rep', 'format', 'find', 'gmatch', 'gsub', 'match', 'sort', 'next', 'pairs', 'ipairs'):
                return S('libcall', fv.name, tuple(vals))
            raise nberror('symbolic math.%s' % fv.name)
        if isinstance(fv, unpack3stub):
            if len(args) == 1:
                v = self.eval(args[0], env, ctx)
                return pack3(v if isinstance(v, lsym) else S('const', v), None)
            raise nberror('unpack3 args %r' % (args,))
        if isinstance(fv, nextstub):
            raise nberror('next() call')
        if isinstance(fv, falsystub):
            return falsystub()
        if isinstance(fv, lsym):
            vals = [self.eval(a, env, ctx) for a in args]
            flat = []
            for v in vals:
                if isinstance(v, tuple):
                    flat.extend((x for x in v if x is not None))
                else:
                    flat.append(v)
            vals = [self.packarg(v) for v in flat]
            return S('call', fv, tuple(vals))
        if callable(fv):
            return fv(*[self.eval(a, env, ctx) for a in args])
        raise nberror('call callee %r' % (fv,))

    def packarg(self, v):
        if isinstance(v, regrange):
            if isinstance(v.a, int) and isinstance(v.b, int) and (v.b >= v.a):
                return S('regs', v.a, v.b)
            return S('regs_top', v.a)
        if isinstance(v, pack3):
            return v.call
        if isinstance(v, falsystub):
            return S('const', None)
        return v

    def resolvemap(self, idx):
        vm = self.vm
        j = idx - 1
        if 0 <= j < len(vm.inlinemap):
            sid = vm.inlinemap[j]
            if sid != 65535:
                return vm.strings.get(sid)
        return None

    def notemissingdouble(self, n):
        pass

    def toint(self, v):
        if isinstance(v, bool):
            raise nberror('bool as int')
        if isinstance(v, int):
            return v
        if isinstance(v, float) and v.is_integer():
            return int(v)
        raise nberror('toint %r' % (v,))

    def symify(self, v):
        if isinstance(v, regrange):
            return self.packarg(v)
        if isinstance(v, tablit):
            if v.base is not None:
                raise nberror('symify slice TabLit')
            return S('tablelit', tuple(sorted(v.items.items(), key=repr)))
        if isinstance(v, lsym):
            return v
        if isinstance(v, falsystub):
            return S('const', None)
        if v is None or isinstance(v, (bool, int, float, str)):
            return S('const', v)
        raise nberror('symify %r' % (v,))

    def condbranch(self, cond, blk, env, ctx):
        c = self.evalcond(cond, env, ctx)
        if c is True or c is False:
            return c
        if isinstance(c, falsystub):
            return False
        if not isinstance(c, (lsym, type(None))):
            return bool(c)
        if c is None:
            return False
        if self.isjumpblock(blk):
            pol = True
            tgt = self.uk.get(ctx.pc)
            ctx.eff('cjump', c, tgt, pol)
            return 'JUMPED'
        if isinstance(c, lsym):
            if symhas(c, 'top') or symhas(c, 'packn'):
                return False
            if c.t == 'type':
                inner = c.a[0]
                return None
            if c.t == 'cmp':
                op, l, r = c.a

                def cv2(x):
                    return x.a[0] if isinstance(x, lsym) and x.t == 'const' else x
                lv, rv = (cv2(l), cv2(r))
                if isinstance(l, lsym) and l.t == 'type' and isinstance(rv, str):
                    return rv == 'function' if op == '==' else rv != 'function'
                if isinstance(r, lsym) and r.t == 'type' and isinstance(lv, str):
                    return lv == 'function' if op == '==' else lv != 'function'
                if isinstance(l, lsym) and l.t == 'type' and (op == '=='):
                    return False
                if isinstance(r, lsym) and r.t == 'type' and (op == '=='):
                    return False
                if r == S('const', None) or l == S('const', None):
                    return op == '~='
                if symhas(c, 'top') or symhas(c, 'packn'):
                    return False
                return None
            if c.t == 'and':
                if hasnilcmp(c):
                    return False
                if hastypecmp(c):
                    return False
                if hassentinelcmp(c):
                    return False
                if symhas(c, 'top') or symhas(c, 'packn'):
                    return False
                return None
            if c.t in ('reg', 'index', 'glob', 'upv'):
                return True
            if c.t == 'not':
                inner = c.a[0]
                if isinstance(inner, lsym) and inner.t in ('reg', 'index', 'glob', 'upv'):
                    return True
                if isinstance(inner, lsym) and inner.t == 'cmp':
                    op, l, r = inner.a
                    if isinstance(l, lsym) and l.t == 'type' and isinstance(r, str):
                        return r != 'function'
                    if r == S('const', None) or l == S('const', None):
                        return op == '=='
                return None
        return None

    def evalcond(self, cond, env, ctx):
        k = cond[0]
        if k == 'bin' and cond[1] in ('==', '~=', '<', '>', '<=', '>='):
            l = self.eval(cond[2], env, ctx)
            r = self.eval(cond[3], env, ctx)
            if isinstance(l, lsym) or isinstance(r, lsym):
                l = l if isinstance(l, lsym) else S('const', l)
                r = r if isinstance(r, lsym) else S('const', r)
                return S('cmp', cond[1], l, r)
            if isinstance(l, falsystub) or isinstance(r, falsystub):
                return cond[1] == '~='
            if cond[1] == '==':
                return l == r
            if cond[1] == '~=':
                return l != r
            if cond[1] == '<':
                return l < r
            if cond[1] == '>':
                return l > r
            if cond[1] == '<=':
                return l <= r
            return l >= r
        return self.eval(cond, env, ctx)

    def isjumpblock(self, blk):
        for st in walkstmts(blk):
            if st[0] == 'assign' and st[1][0] == ('name', 'PC'):
                rhs = st[2][0]
                if rhs[0] == 'index' and rhs[1] == ('name', 'UK'):
                    return True
                if rhs[0] == 'bin' and rhs[1] in ('+', '-') and (rhs[2] == ('name', 'PC') or rhs[3] == ('name', 'PC')):
                    return True
                if rhs == ('name', 'PC'):
                    return False
                if rhs[0] == 'name':
                    return True
        return False
ignoredwrites = {'MU', 'Q4', 'MM', 'zg', 'zh', 'Is', 'Iq', 'xL', 'xo', 'xQ', 'xu', 'QB'}

class stublib:

    def __init__(self, dec):
        self.dec = dec

    def getstub(self, k):
        return stubtab(self.dec).getstub(k)

    def getstubname(self, kv):
        raise nberror('stublib[%r]' % (kv,))

class keyid:

    def __getitem__(self, k):
        return k

def vfixedorpackn(pack):
    if pack.fixed is not None:
        return pack.fixed
    return S('packn', pack)

def walkstmts(blk):
    for st in blk:
        yield st
        if st[0] == 'if':
            for c, b in st[1]:
                for x in walkstmts(b):
                    yield x
            if st[2]:
                for x in walkstmts(st[2]):
                    yield x
        elif st[0] == 'while':
            for x in walkstmts(st[2]):
                yield x
        elif st[0] == 'fornum':
            for x in walkstmts(st[5]):
                yield x
        elif st[0] == 'forin':
            for x in walkstmts(st[3]):
                yield x
        elif st[0] == 'do':
            for x in walkstmts(st[1]):
                yield x
special = {}
nbtemplates = []
varargloadre = re.compile("MJ\\[zD\\]|Q9\\[IE\\]|MJ\\['n'\\]|Q9\\['n'\\]")
callselfvarre = re.compile('for (\\w+)=1,\\w+ do (\\w+)\\[\\1\\]=R\\[\\w+\\+\\1\\]end')

def spnop(dec, i, o):
    return {'i': i, 'op': o.get('opid'), 'kind': 'NOP', 'effects': [], 'newpc': None}
callselfshape = re.compile('\\w+=@0\\[PC\\]\\w+=@1\\[PC\\]\\w+=@2\\[PC\\]-1\\s*\\w+=@3\\[PC\\]-1')

def spcallselfvar(dec, i, o):
    nb = o['nb']
    if not callselfshape.search(nb):
        raise nberror('callself shape mismatch')
    if not re.search('=\\w+ and \\w+\\[\\w+\\]or nil', nb):
        raise nberror('callself self-marker missing')
    cols = cols2(dec, i)
    A, B, C, D = (cols[0], cols[1], cols[2], cols[3])
    k = dec.resolvemap(cols[4] + cols[5] * 256 + 1)
    callee = S('and', S('reg', B), S('index', S('reg', B), S('const', k)))
    if C == 0:
        args = (S('regs_top', A + 1),)
    else:
        args = (S('regs', A + 1, A + C - 1),) if C > 2 else tuple((S('reg', A + j) for j in range(1, C))) or (S('const', None),)
    call = S('call', callee, args)
    eff = [('set', S('reg', A), callee), ('set', S('reg', A + 1), S('reg', B))]
    if D == 0:
        eff.append(('setm', A, call))
    elif D == 1:
        eff.append(('expr', call))
    else:
        for j in range(D - 1):
            eff.append(('set', S('reg', A + j), S('callres', call, j)))
    return {'i': i, 'op': o.get('opid'), 'kind': 'CALL', 'effects': eff, 'newpc': None}

def sbx16(cols, lo, hi):
    v = cols[lo] + cols[hi] * 256
    return v - 65536 if v >= 32768 else v

def ufxtarget(dec, i, own, sbx):
    off = dec.uf.get(i)
    if off is None:
        return None
    return dec.ufx.get(off + own + sbx)

def ownsize(nb):
    m = re.search('\\w\\+(\\d+)\\+\\w', nb)
    return int(m.group(1)) if m else 4

def cols2(dec, i):
    return [dec.P['regs'][c].get(i) or 0 for c in range(8)]

def spforprep(dec, i, o):
    cols = cols2(dec, i)
    A = cols[0]
    own = ownsize(o['nb'])
    sbx = sbx16(cols, 1, 2)
    tgt = ufxtarget(dec, i, own, sbx)
    if tgt is None:
        raise nberror('FORPREP target unresolved (sbx=%d)' % sbx)
    role = 'forprep' if tgt > i else 'forloop'
    return {'i': i, 'op': o.get('opid'), 'kind': o['kind'], 'effects': [], role: {'a': A, 'target': tgt, 'sbx': sbx}, 'newpc': tgt}

def sptforprep(dec, i, o):
    cols = cols2(dec, i)
    A = cols[0]
    own = ownsize(o['nb'])
    sbx = sbx16(cols, 1, 2)
    tgt = ufxtarget(dec, i, own, sbx)
    if tgt is None:
        raise nberror('TFORPREP target unresolved (sbx=%d)' % sbx)
    return {'i': i, 'op': o.get('opid'), 'kind': o['kind'], 'effects': [], 'tforprep': {'a': A, 'target': tgt}, 'newpc': tgt}

def sptforloop(dec, i, o):
    cols = cols2(dec, i)
    A = cols[0]
    nout = cols[3]
    sel = cols[5]
    sbx = sbx16(cols, 1, 2)
    tgt = ufxtarget(dec, i, 8, sbx)
    if tgt is None:
        raise nberror('TFORLOOP target unresolved (sbx=%d)' % sbx)
    return {'i': i, 'op': o.get('opid'), 'kind': o['kind'], 'effects': [], 'tforloop': {'a': A, 'nout': nout, 'sel': sel, 'target': tgt}, 'newpc': tgt}
closuresftail = re.compile('\\w+\\[\\w+\\]=R\\[@3\\[PC\\]\\]')

def spclosure(dec, i, o):
    nb = o['nb']
    if closuresftail.search(nb):
        return spclosuresf(dec, i, o)
    cols = cols2(dec, i)
    idx = cols[1] + cols[2] * 256
    return {'i': i, 'op': o.get('opid'), 'kind': 'CLOSURE', 'effects': [('set', S('reg', cols[0]), S('closure', idx))], 'newpc': None}

def spclosuresf(dec, i, o):
    cols = cols2(dec, i)
    dest = cols[3]
    idx = cols[4] + cols[5] * 256
    base = cols[0]
    kc = cols[1] + cols[2] * 256
    key = dec.resolvemap(kc + 1)
    eff = [('set', S('reg', dest), S('closure', idx))]
    eff.append(('set', S('index', S('reg', base), S('const', key)), S('reg', dest)))
    return {'i': i, 'op': o.get('opid'), 'kind': 'CLOSURE_SETFIELD', 'effects': eff, 'newpc': None}

def spsetlist(dec, i, o):
    cols = cols2(dec, i)
    A, B, C = (cols[0], cols[1], cols[2])
    start = cols[3] + cols[4] * 256 + cols[5] * 65536 + cols[6] * 16777216
    return {'i': i, 'op': o.get('opid'), 'kind': 'SETLIST', 'effects': [('setlist', A, B, C, start)], 'newpc': None}

def spnewtablekeys(dec, i, o):
    cols = cols2(dec, i)
    A = cols[0]
    nb = o['nb']
    kid = None
    m = re.search('if\\(@6\\[PC\\]or 0\\)==0 then \\w+=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256\\w+=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256', nb)
    if m and '@3[PC]=XOR' in nb:
        m1 = (i * int(m.group(1)) + int(m.group(2))) % 256
        m2 = (i * int(m.group(3)) + int(m.group(4))) % 256
        kid = (cols[1] ^ m1) + (cols[2] ^ m2) * 256
    else:
        kid = cols[1] + cols[2] * 256
    keys = dec.sem.keylists.get(kid)
    eff = [('newtable_keys', A, kid, keys if keys is not None else None)]
    if 'R[Uo]=rI' in nb or re.search('R\\[\\w\\]=rI\\b', nb):
        k1 = dec.resolvemap(cols[3])
        v1 = dec.resolvemap(cols[4])
        k2 = dec.resolvemap(cols[5])
        v2 = dec.resolvemap(cols[6])
        eff.append(('set', S('reg', A + 1), S('const', v2)))
        eff.append(('set', S('index', S('reg', A), S('const', k1)), S('const', v1)))
        eff.append(('set', S('index', S('reg', A), S('const', k2)), S('const', v2)))
    return {'i': i, 'op': o.get('opid'), 'kind': o['kind'], 'effects': eff, 'newpc': None}

def sploadlib(dec, i, o):
    cols = cols2(dec, i)
    A = cols[0]
    nb = o['nb']
    if i + 1 > dec.P['n']:
        raise nberror('LOADLIB at end of proto')
    nextop = dec.P['ops'][i]
    gate = re.search('(?:MZ|bQ)\\[PC\\+1\\]==(\\d+) or (?:MZ|bQ)\\[PC\\+1\\]==(\\d+) or (?:MZ|bQ)\\[PC\\+1\\]==(\\d+)', nb)
    if gate:
        allowed = {int(gate.group(k)) for k in (1, 2, 3)}
        if nextop not in allowed:
            return {'i': i, 'op': o.get('opid'), 'kind': 'LOADLIB', 'effects': [], 'newpc': None}
    dest = dec.P['regs'][0].get(i + 1)
    return {'i': i, 'op': o.get('opid'), 'kind': 'LOADLIB', 'effects': [('set', S('reg', dest), S('lib', A))], 'newpc': None}

def spvarargprep(dec, i, o):
    return {'i': i, 'op': o.get('opid'), 'kind': 'VARARG_PREP', 'effects': [], 'newpc': None}

def spvarargload(dec, i, o):
    cols = cols2(dec, i)
    A, B = (cols[0], cols[1])
    return {'i': i, 'op': o.get('opid'), 'kind': 'VARARG', 'effects': [('vararg', A, B)], 'newpc': None}

def spcmp(dec, i, o):
    nb = o['nb']
    cols = cols2(dec, i)
    reads = re.findall('(\\w+)=R\\[@(\\d)\\[PC\\]\\]', nb)
    cmpm = re.search('(\\w+)(==|~=|<=|>=|<|>)(\\w+)', nb)
    if not reads or not cmpm:
        raise nberror('CMP template miss')
    varcol = {v: int(c) for v, c in reads}
    lhs, op, rhs = (cmpm.group(1), cmpm.group(2), cmpm.group(3))
    lcol, rcol = (varcol.get(lhs), varcol.get(rhs))
    if lcol is None or rcol is None:
        raise nberror('CMP cols unresolved %r %r' % (lhs, rhs))
    neg = 'not(' in nb[max(0, cmpm.start() - 5):cmpm.start()]
    tgt = dec.ue.get(i)
    return {'i': i, 'op': o.get('opid'), 'kind': 'CMP', 'effects': [('cjump', S('cmp', op, S('reg', cols[lcol]), S('reg', cols[rcol])), tgt, not neg)], 'newpc': None}

def spcmpconst(dec, i, o):
    nb = o['nb']
    cols = cols2(dec, i)
    m = re.search('\\w+=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256\\w+=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256\\w+=XOR\\(@4\\[PC\\],\\w+\\)\\+\\(XOR\\(@5\\[PC\\],\\w+\\)\\*256\\)', nb)
    if not m:
        raise nberror('CMP_CONST const unresolved')
    m1 = (i * int(m.group(1)) + int(m.group(2))) % 256
    m2 = (i * int(m.group(3)) + int(m.group(4))) % 256
    kc = (cols[4] ^ m1) + (cols[5] ^ m2) * 256
    val = dec.resolvemap(kc + 1)
    reads = re.findall('(\\w+)=R\\[@(\\d)\\[PC\\]\\]', nb)
    cmpm = re.search('(\\w+)(==|~=|<=|>=|<|>)(\\w+)', nb)
    if not reads or not cmpm:
        raise nberror('CMP_CONST cmp unresolved')
    varcol = {v: int(c) for v, c in reads}
    lhs, op, rhs = (cmpm.group(1), cmpm.group(2), cmpm.group(3))
    lcol, rcol = (varcol.get(lhs), varcol.get(rhs))
    if lcol is None or rcol is None:
        raise nberror('CMP_CONST cols')
    neg = 'not(' in nb[max(0, cmpm.start() - 5):cmpm.start()]
    tgt = dec.ue.get(i)
    eff = [('set', S('reg', cols[1]), S('const', val))]
    eff.append(('cjump', S('cmp', op, S('reg', cols[lcol]), S('reg', cols[rcol])), tgt, not neg))
    return {'i': i, 'op': o.get('opid'), 'kind': 'CMP_CONST', 'effects': eff, 'newpc': None}

def spconcat(dec, i, o):
    cols = cols2(dec, i)
    A, B, C = (cols[0], cols[1], cols[2])
    return {'i': i, 'op': o.get('opid'), 'kind': 'CONCAT', 'effects': [('set', S('reg', A), S('concat', B, C))], 'newpc': None}

def spclose(dec, i, o):
    return {'i': i, 'op': o.get('opid'), 'kind': 'CLOSE', 'effects': [], 'newpc': None}
special['FORPREP'] = spforprep
special['TFORPREP'] = sptforprep
special['TFORLOOP'] = sptforloop
special['CLOSURE'] = spclosure
special['CLOSURE_SETFIELD'] = spclosuresf
special['SETLIST'] = spsetlist
special['LOADLIB'] = sploadlib
special['VARARG_PREP'] = spvarargprep
special['VARARG'] = spvarargload
special['CMP'] = spcmp
special['CMP_CONST'] = spcmpconst
special['CONCAT'] = spconcat
special['CLOSE'] = spclose
special['NOP'] = spnop
callglobalvarre = re.compile('UP=ENV\\[\\w+\\]R\\[Uw\\]=UP')
callglobalshape = re.compile('\\w+=\\(\\w+%16\\)-1 \\w+=n8\\[zk\\[17816\\]\\]\\(\\w+/16\\)-1')

def spcallglobalvar(dec, i, o):
    nb = o['nb']
    if not callglobalshape.search(nb):
        raise nberror('callglobal shape mismatch')
    cols = cols2(dec, i)
    A, B, rf = (cols[0], cols[1], cols[2])
    nargs = rf % 16 - 1
    nrets = rf // 16 - 1
    m = re.search('\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256\\w+=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%256\\w+=XOR\\(@3\\[PC\\],\\w+\\)\\+\\(XOR\\(@4\\[PC\\],\\w+\\)\\*256\\)\\w+=XOR\\(@5\\[PC\\],\\w+\\)\\+\\(XOR\\(@6\\[PC\\],\\w+\\)\\*256\\)', nb)
    if not m:
        raise nberror('callglobal masks')
    m1 = (i * int(m.group(1)) + int(m.group(2))) % 256
    m2 = (i * int(m.group(3)) + int(m.group(4))) % 256
    g = dec.resolvemap((cols[3] ^ m1) + (cols[4] ^ m2) * 256 + 1)
    k = dec.resolvemap((cols[5] ^ m1) + (cols[6] ^ m2) * 256 + 1)
    callee = S('index', S('glob', g), S('const', k))
    if nargs == -1:
        args = (S('regs_top', A + 1),)
    elif nargs >= 1:
        args = (S('regs', A + 1, A + nargs),)
    else:
        args = (S('const', None),)
    call = S('call', callee, args)
    eff = [('set', S('reg', B), S('glob', g)), ('set', S('reg', A), S('index', S('reg', B), S('const', k)))]
    if nrets == -1:
        eff.append(('setm', A, call))
    elif nrets == 0:
        eff.append(('expr', call))
    else:
        for j in range(nrets):
            eff.append(('set', S('reg', A + j), S('callres', call, j)))
    return {'i': i, 'op': o.get('opid'), 'kind': 'CALL', 'effects': eff, 'newpc': None}
nbtemplates.append((varargloadre, spvarargload))
nbtemplates.append((callglobalvarre, spcallglobalvar))
nbtemplates.append((callselfvarre, spcallselfvar))
