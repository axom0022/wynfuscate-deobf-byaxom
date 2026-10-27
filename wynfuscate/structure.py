from __future__ import annotations
from .semant import L, loadlibtable
from .nb import collectnamesfromnbs
from .ir import irdecoder, lsym
from .emit import emitter2, walksyms

maxregmargin = 4

class line2:
    __slots__ = ('pc', 'kind', 'op', 'stmts', 'cjump', 'newpc', 'ret', 'forprep', 'forloop', 'tforprep', 'tforloop', 'defs')

    def __init__(self, pc, d):
        self.pc = pc
        self.kind = d.get('kind', '?')
        self.op = d.get('op')
        self.stmts = []
        self.cjump = None
        self.newpc = d.get('newpc')
        self.ret = None
        self.forprep = d.get('forprep')
        self.forloop = d.get('forloop')
        self.tforprep = d.get('tforprep')
        self.tforloop = d.get('tforloop')
        self.defs = None
        for e in d.get('effects', []):
            t = e[0]
            if t == 'set':
                self.stmts.append((e[1], e[2]))
            elif t == 'cjump':
                self.cjump = (e[1], e[2], e[3])
            elif t == 'expr':
                self.stmts.append((None, e[1]))
            elif t == 'setm':
                self.stmts.append((('setm', e[1]), e[2]))
            elif t == 'setlist':
                self.stmts.append((('setlist',) + tuple(e[1:]), None))
            elif t == 'vararg':
                self.stmts.append((('vararg',) + tuple(e[1:]), None))
            elif t == 'return':
                self.ret = ('return', e[1], e[2]) if len(e) == 3 else ('return',)
            elif t == 'returnm':
                self.ret = ('returnm', e[1])
            elif t == 'returnvals':
                self.ret = ('returnvals', e[1])
            elif t == 'returnraw':
                self.ret = ('returnraw', e[1])
            else:
                self.stmts.append((('raw', t, e[1:]), None))

def buildlines(dec, P):
    return {i: line2(i, dec.decode(i)) for i in range(1, P['n'] + 1)}

class defstate:
    __slots__ = ('kind', 'src', 'base')

    def __init__(self, kind, src=None, base=None):
        self.kind = kind
        self.src = src
        self.base = base

def mergepass(lines, nregs):
    defs = [None] * (nregs + 8)
    for pc in sorted(lines):
        L = lines[pc]
        L.defs = list(defs)
        newdefs = {}
        for tgt, val in L.stmts:
            if isinstance(tgt, lsym) and tgt.t == 'reg':
                n = tgt.a[0]
                if isinstance(val, lsym) and val.t == 'callres':
                    newdefs[n] = defstate('pack', val.a[0])
                else:
                    newdefs[n] = defstate('sym', val)
            elif isinstance(tgt, tuple) and tgt[0] == 'setm':
                base = tgt[1]
                for k in range(0, len(defs) - base):
                    newdefs[base + k] = defstate('pack', val)
            elif isinstance(tgt, tuple) and tgt[0] == 'vararg' and (tgt[2] == 0):
                base = tgt[1]
                for k in range(0, len(defs) - base):
                    newdefs[base + k] = defstate('va', None, base)
        if L.ret and L.ret[0] == 'returnm':
            base = L.ret[1]
            L.ret = ('returnm', base, defs[base] if 0 <= base < len(defs) else None)
        for n, d in newdefs.items():
            defs[n] = d

class structurer:

    def __init__(self, lines, n, emitter):
        self.lines = lines
        self.n = n
        self.em = emitter
        self.succ = {}
        for i in range(1, n + 1):
            L = lines[i]
            if L.ret:
                self.succ[i] = []
                continue
            if L.forprep:
                self.succ[i] = [i + 1, L.forprep['target']]
            elif L.tforprep:
                self.succ[i] = [i + 1, L.tforprep['target']]
            elif L.forloop:
                self.succ[i] = [i + 1, L.forloop['target']]
            elif L.tforloop:
                self.succ[i] = [i + 1, L.tforloop['target']]
            elif L.cjump:
                t = L.cjump[1]
                self.succ[i] = [i + 1] + ([t] if t and t != i + 1 else [])
            elif L.newpc is not None and L.newpc != i + 1:
                self.succ[i] = [L.newpc]
            else:
                self.succ[i] = [i + 1]
            self.succ[i] = [x for x in self.succ[i] if 1 <= x <= n + 1]
        self.reach = set()
        stack = [1]
        while stack:
            x = stack.pop()
            if x in self.reach or x < 1 or x > n:
                continue
            self.reach.add(x)
            for t in self.succ.get(x, []):
                if 1 <= t <= n:
                    stack.append(t)
        self.pairs = []
        used = set()
        for i in sorted(self.lines):
            L = self.lines[i]
            if i not in self.reach:
                continue
            if L.forprep:
                A = L.forprep['a']
                for q in sorted(self.lines):
                    if q <= i or q in used:
                        continue
                    M = self.lines[q]
                    if M.forloop and M.forloop['a'] == A and (M.forloop['target'] == i + 1):
                        self.pairs.append((i, q, 'for'))
                        used.update((i, q))
                        break
            if L.tforprep:
                A = L.tforprep['a']
                for q in sorted(self.lines):
                    if q <= i or q in used:
                        continue
                    M = self.lines[q]
                    if M.tforloop and M.tforloop['a'] == A and (M.tforloop['target'] == i + 1):
                        self.pairs.append((i, q, 'tfor'))
                        used.update((i, q))
                        break
        self.pairhead = {p: (q, k) for p, q, k in self.pairs}
        self.pairtail = {q: p for p, q, k in self.pairs}
        self.back = {}
        for i in sorted(self.lines):
            if i not in self.reach or i in self.pairtail:
                continue
            L = self.lines[i]
            t = None
            if L.cjump:
                t = L.cjump[1]
            elif L.newpc is not None and L.newpc != i + 1:
                t = L.newpc
            if t is not None and 1 <= t <= i:
                self.back.setdefault(t, []).append(i)
        self.afterif = None

    def condtext(self, cond, pol):
        t = self.em.expr(cond)
        return t if pol else 'not (%s)' % t

    def structure(self, lo, hi, loopstack):
        out = []
        pc = lo
        while pc <= hi:
            if pc not in self.reach:
                pc += 1
                continue
            L = self.lines.get(pc)
            if L is None:
                break
            if pc in self.pairhead:
                q, kind = self.pairhead[pc]
                if q > hi:
                    out.append('-- loop pair OOB p=%d q=%d' % (pc, q))
                    pc += 1
                    continue
                out.extend(self.emitpair(pc, q, kind, loopstack))
                pc = q + 1
                continue
            if pc in self.pairtail:
                pc += 1
                continue
            heads = [t for t in self.back if lo <= t <= hi and any((lo <= b <= hi for b in self.back[t]))]
            if pc in heads:
                cands = [b for b in self.back[pc] if lo <= b <= hi]
                if cands:
                    b = max(cands)
                    out.extend(self.emitloop(pc, b, loopstack, hi))
                    pc = b + 1
                    continue
            if L.cjump:
                cond, t, pol = L.cjump
                if t is None or t == pc + 1 or t == pc:
                    out.extend(self.emitline(L))
                    pc = self.advance(pc, hi)
                    continue
                if t == hi + 1:
                    body = self.structure(pc + 1, hi, loopstack)
                    out.append('if %s then' % self.condtext(cond, not pol))
                    out.extend(('    ' + x for x in body))
                    out.append('end')
                    pc = hi + 1
                    continue
                if t > hi:
                    out.extend(self.emitline(L))
                    ok = False
                    if loopstack:
                        head, exitp = loopstack[-1]
                        if t == exitp:
                            out.append('if %s then break end' % self.condtext(cond, pol))
                            ok = True
                    if not ok:
                        out.append('-- jump %d -> %d (cond %s) unstructured' % (pc, t, self.condtext(cond, pol)))
                    pc = self.advance(pc, hi)
                    continue
                out.extend(self.emitif(pc, t, loopstack))
                pc = self.afterif
                continue
            if L.newpc is not None and L.newpc != pc + 1 and (not L.stmts):
                t = L.newpc
                if t < pc:
                    return out
                out.append('-- fwd jump %d -> %d' % (pc, t))
                pc = max(t, pc + 1)
                continue
            out.extend(self.emitline(L))
            pc = self.advance(pc, hi)
        return out

    def advance(self, pc, hi):
        pc += 1
        while pc <= hi and pc not in self.reach:
            pc += 1
        return pc

    def emitpair(self, p, q, kind, loopstack):
        em = self.em
        out = []
        P = self.lines[p]
        Q = self.lines[q]
        if kind == 'for':
            A = P.forprep['a']
            var = em.regname(A + 2)
            if not var.isidentifier():
                var = em.newtmp('i')
            out.append('for %s = %s, %s, %s do' % (var, em.regname(A + 2), em.regname(A), em.regname(A + 1)))
            inner = self.structure(p + 1, q - 1, loopstack + [(p, q + 1)])
            out.extend(('    ' + x for x in inner))
            out.append('end')
        else:
            A = P.tforprep['a']
            nout = Q.tforloop.get('nout', 2) or 2
            names = [em.newtmp('k') for _ in range(max(nout, 1))]
            saved = {}
            for idx, nm in enumerate(names):
                saved[A + 3 + idx] = em.rn.get(A + 3 + idx)
                em.bindreg(A + 3 + idx, nm)
            out.append('for %s in %s, %s, %s do' % (', '.join(names), em.regname(A), em.regname(A + 1), em.regname(A + 2)))
            inner = self.structure(p + 1, q - 1, loopstack + [(p, q + 1)])
            out.extend(('    ' + x for x in inner))
            out.append('end')
            for r, old in saved.items():
                if old is None:
                    em.rn.pop(r, None)
                else:
                    em.rn[r] = old
        return out

    def emitloop(self, head, tail, loopstack, hi):
        out = []
        em = self.em
        H = self.lines[head]
        T = self.lines[tail]
        exitp = tail + 1
        if H.cjump and H.cjump[1] == exitp:
            cond, t, pol = H.cjump
            pre = self.emitline(H)
            out.extend(pre)
            out.append('while true do')
            inner = ['if %s then break end' % self.condtext(cond, pol)]
            inner.extend(self.structure(head + 1, tail - 1, loopstack + [(head, exitp)]))
            out.extend(('    ' + x for x in inner))
            out.append('end')
        else:
            out.append('while true do')
            inner = []
            inner.extend(self.structure(head, tail - 1, loopstack + [(head, exitp)]))
            inner.extend(self.emitstmts(T))
            if T.cjump:
                cond, t, pol = T.cjump
                if t == head:
                    c = self.condtext(cond, not pol)
                    inner.append('if %s then break end' % c)
                else:
                    inner.append('-- odd tail cjump %d -> %d' % (tail, t))
                    inner.append('if %s then break end' % self.condtext(cond, pol))
            elif T.newpc is not None and T.newpc == head:
                pass
            else:
                inner.append('-- tail %d unhandled' % tail)
            out.extend(('    ' + x for x in inner))
            out.append('end')
        return out

    def emitif(self, pc, t, loopstack):
        L = self.lines[pc]
        cond, target, pol = L.cjump
        em = self.em
        out = []
        elsejump = None
        M = self.lines.get(t - 1) if t - 1 > pc else None
        if M is not None and M.newpc is not None and (M.newpc > t) and (not M.stmts) and (M.newpc <= self.n + 1) and (t - 1 not in self.pairtail) and (not M.cjump) and (not M.ret):
            elsejump = M.newpc
        if elsejump is not None:
            m = elsejump
            thenbody = self.structure(t, m - 1, loopstack)
            elsebody = self.structure(pc + 1, t - 2, loopstack)
            out.append('if %s then' % self.condtext(cond, pol))
            out.extend(('    ' + x for x in thenbody))
            if elsebody:
                out.append('else')
                out.extend(('    ' + x for x in elsebody))
            out.append('end')
            self.afterif = m
        else:
            body = self.structure(pc + 1, t - 1, loopstack)
            out.append('if %s then' % self.condtext(cond, not pol))
            out.extend(('    ' + x for x in body))
            out.append('end')
            self.afterif = t
        return out

    def emitline(self, L):
        return self.emitstmts(L)

    def emitstmts(self, L):
        em = self.em
        em.curdefs = L.defs
        out = []
        if not L.ret:
            needed = []
            for tgt, val in L.stmts:
                sy = []
                walksyms((tgt, val), sy)
                for s in sy:
                    call = None
                    if s.t == 'callres':
                        call = s.a[0]
                    elif s.t == 'packn' and isinstance(s.a[0], lsym) and (s.a[0].t == 'call'):
                        call = s.a[0]
                    if isinstance(call, lsym) and call.t == 'call' and (id(call) not in em.declaredpacks):
                        em.declaredpacks.add(id(call))
                        needed.append(call)
            for call in needed:
                pk = em.packvar(call)
                out.append('local %s = table.pack(%s)' % (pk, em.calltext(call)))
        if L.ret:
            r = L.ret
            if r[0] == 'return':
                if len(r) >= 3 and isinstance(r[2], int) and (r[2] >= r[1]):
                    body = 'return ' + ', '.join((em.regname(x) for x in range(r[1], r[2] + 1)))
                elif len(r) >= 3:
                    body = 'return ' + em.regname(r[1])
                else:
                    body = 'return'
            elif r[0] == 'returnm':
                base = r[1]
                d = r[2] if len(r) > 2 else None
                if d is not None and d.kind == 'pack':
                    pk = em.packvar(d.src)
                    body = 'return table.unpack(%s, 1, %s.n)' % (pk, pk)
                elif d is not None and d.kind == 'va':
                    body = 'return ...'
                else:
                    body = 'return table.unpack(%s)' % em.regname(base)
            elif r[0] == 'returnvals':
                body = 'return ' + ', '.join((em.expr(x) for x in r[1]))
            else:
                body = 'return -- raw'
            out.append('do ' + body + ' end')
            return out
        uses = {}
        for tgt, val in L.stmts:
            if isinstance(val, lsym) and val.t == 'call':
                uses[id(val)] = uses.get(id(val), 0) + 1
        em.linematerialized = {}
        em.matpool = []
        for tgt, val in L.stmts:
            if isinstance(val, lsym) and val.t == 'call' and (uses.get(id(val), 0) > 1):
                if id(val) not in em.linematerialized:
                    t = 'c%s_%d' % (em.pfx, len(em.matpool) + 1)
                    em.matpool.append(t)
                    out.append('local %s = %s' % (t, em.calltext(val)))
                    em.linematerialized[id(val)] = t
        for tgt, val in L.stmts:
            if isinstance(tgt, lsym) and tgt.t == 'reg':
                n = tgt.a[0]
                out.append('%s = %s' % (em.regname(n), self.valtext(val, L)))
            elif isinstance(tgt, lsym) and tgt.t == 'upv':
                out.append('%s = %s' % (em.upvname(tgt.a[0]), self.valtext(val, L)))
            elif isinstance(tgt, lsym) and tgt.t in ('index', 'glob'):
                out.append('%s = %s' % (em.expr(tgt), self.valtext(val, L)))
            elif tgt is None:
                t = self.valtext(val, L)
                out.append('; ' + t if t.startswith('(') else t)
            elif isinstance(tgt, tuple):
                out.extend(self.emitspecial(tgt, val, L))
            else:
                out.append('-- ?stmt')
        return out

    def valtext(self, val, L):
        em = self.em
        if isinstance(val, lsym) and val.t == 'call':
            t = getattr(em, 'linematerialized', {}).get(id(val))
            if t:
                return t
        if isinstance(val, lsym) and val.t == 'regs_top':
            base = val.a[0]
            d = L.defs[base] if L.defs and 0 <= base < len(L.defs) else None
            if d is not None and d.kind == 'pack':
                pk = em.packvar(d.src)
                return 'table.unpack(%s, 1, %s.n)' % (pk, pk)
            if d is not None and d.kind == 'va':
                va = em.ensureva()
                return 'table.unpack(%s, 1, %s.n)' % (va, va)
            if d is not None and d.kind == 'sym':
                parts = []
                i = base
                while i < len(L.defs) and L.defs[i] is not None and (L.defs[i].kind == 'sym'):
                    parts.append(em.regname(i))
                    i += 1
                if i < len(L.defs) and L.defs[i] is not None and (L.defs[i].kind == 'pack'):
                    pk = em.packvar(L.defs[i].src)
                    parts.append('table.unpack(%s, 1, %s.n)' % (pk, pk))
                    return ', '.join(parts)
                if i < len(L.defs) and L.defs[i] is not None and (L.defs[i].kind == 'va'):
                    va = em.ensureva()
                    parts.append('table.unpack(%s, 1, %s.n)' % (va, va))
                    return ', '.join(parts)
            return 'table.unpack(TOPMARK_%d)' % base
        return em.expr(val)

    def emitspecial(self, tgt, val, L):
        em = self.em
        out = []
        if tgt[0] == 'setm':
            pk = em.packvar(val)
            out.append('local %s = table.pack(%s)' % (pk, em.calltext(val)))
        elif tgt[0] == 'vararg':
            base, b = (tgt[1], tgt[2])
            va = em.ensureva()
            out.append('local %s = table.pack(...)' % va)
        elif tgt[0] == 'setlist':
            A, B, C, start = (tgt[1], tgt[2], tgt[3], tgt[4])
            if C and C > 0:
                tv = em.newtmp('sl')
                out.append('for %s = 1, %d do' % (tv, C))
                out.append('    %s[%d + %s - 1] = %s' % (em.regname(A), start, tv, em.regname(B)))
                out.append('end')
            else:
                d = L.defs[B] if L.defs and 0 <= B < len(L.defs) else None
                if d is not None and d.kind == 'pack':
                    pk = em.packvar(d.src)
                    out.append('for %s = 1, %s.n do' % (em.newtmp('sl'), pk))
                    out.append('    %s[%d + %s - 1] = %s[%s]' % (em.regname(A), start, 'sl', pk, 'sl'))
                    out.append('end')
                elif d is not None and d.kind == 'sym':
                    i = B
                    off = start
                    while i < len(L.defs) and L.defs[i] is not None and (L.defs[i].kind == 'sym'):
                        out.append('%s[%d] = %s' % (em.regname(A), off, em.regname(i)))
                        i += 1
                        off += 1
                    if i < len(L.defs) and L.defs[i] is not None and (L.defs[i].kind == 'pack'):
                        pk = em.packvar(L.defs[i].src)
                        tv = em.newtmp('sl')
                        out.append('for %s = 1, %s.n do' % (tv, pk))
                        out.append('    %s[%d + %s - 1] = %s[%s]' % (em.regname(A), off, tv, pk, tv))
                        out.append('end')
                    else:
                        out.append('-- setlist-top A=%d B=%d' % (A, B))
                else:
                    out.append('-- setlist-top A=%d B=%d' % (A, B))
        else:
            out.append('-- special %r' % (tgt,))
        return out

    def run(self):
        return self.structure(1, self.n, [])

class lifter2:

    def __init__(self, sem):
        self.sem = sem
        self.vm = sem.vm
        self.cache = {}
        self.depth = 0
        self.closurebody = {}

    def loadlibname(self, a):
        return loadlibtable.get(a, 'libfn_%s' % a)

    def upvresolverfor(self, parentem, childpid):
        P = self.vm.protos[childpid]
        ups = P.get('upvals', [])

        def resolve(k):
            if k < len(ups):
                inreg, idx = ups[k]
                if inreg:
                    return parentem.regname(idx)
                return parentem.upvname(idx)
            return parentem.regname(k)
        return resolve

    def closuretext(self, idx, parentem):
        return self.liftchild(idx, self.upvresolverfor(parentem, idx), parentem)

    def liftchild(self, pid, upvresolver, parentem):
        self.depth += 1
        try:
            if self.depth > 60:
                return 'function() end -- too deep'
            text = self.liftproto(pid, upvresolver)
            return text
        finally:
            self.depth -= 1

    def liftproto(self, pid, upvresolver=None):
        P = self.vm.protos[pid]
        dec = irdecoder(self.sem, P)
        lines = buildlines(dec, P)
        mx = 0
        for i, L in lines.items():
            for tgt, val in L.stmts:
                sy = []
                walksyms((tgt, val), sy)
                for s in sy:
                    if s.t == 'reg':
                        mx = max(mx, s.a[0])
                    elif s.t == 'regs' and isinstance(s.a[0], int) and isinstance(s.a[1], int):
                        mx = max(mx, s.a[1])
                    elif s.t == 'regs_top':
                        mx = max(mx, s.a[0] + 1)
            for mk in (L.forprep, L.forloop, L.tforprep, L.tforloop):
                if isinstance(mk, dict):
                    a = mk.get('a', 0)
                    nout = mk.get('nout', 0) or 0
                    mx = max(mx, a + 2, a + 2 + max(nout, 1))
            if L.ret and L.ret[0] == 'return' and (len(L.ret) >= 3) and isinstance(L.ret[2], int):
                mx = max(mx, L.ret[2])
        nregs = mx + 1
        mergepass(lines, nregs)
        em = emitter2(self, pid, upvresolver)
        em.spill = 100 if nregs > 150 else None
        params = []
        for k in range(P['numparams']):
            nm = 'ap%d_%d' % (pid, k)
            params.append(nm)
            em.bindreg(k, nm)
        if P['is_vararg']:
            params.append('...')
        st = structurer(lines, P['n'], em)
        body = st.run()
        out = ['function(%s)' % ', '.join(params)]
        if em.spill is not None:
            out.append('    local %s = {}' % em.rptab)
            decls = [em.regname(k) for k in range(P['numparams'], em.spill)]
            if decls:
                out.append('    local ' + ', '.join(decls))
        else:
            decls = [em.regname(k) for k in range(P['numparams'], nregs)]
            if decls:
                out.append('    local ' + ', '.join(decls))
        out.extend(('    ' + x for x in body))
        out.append('end')
        return '\n'.join(out)

def liftscriptgen2(sem):
    nbs = [o['nb'] for o in sem.ops.values() if o.get('nb')]
    collectnamesfromnbs(nbs)
    lifter = lifter2(sem)
    main = lifter.liftproto(0)
    prelude = "-- [[ deobfuscated by Axomic wynfuscate deobfuscation | our YouTube channel : https://youtube.com/@axos0022 | our discord server : https://discord.gg/axomx / https://discord.gg/Sps39CydcZ ]]\nlocal select, type, unpack, pairs, next, tostring, tonumber = select, type, unpack, pairs, next, tostring, tonumber\nlocal table, math, string = table, math, string\nif not table.unpack then table.unpack = unpack end\nif not table.pack then\n  function table.pack(...) return { n = select('#', ...), ... } end\nend\nlocal _G = getfenv and getfenv() or _G\n"
    return prelude + '\nlocal main = ' + main + '\nmain(...)\n'
