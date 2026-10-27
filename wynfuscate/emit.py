from __future__ import annotations
import re
from .ir import S, lsym

keywords = {'and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function', 'if', 'in', 'local', 'nil', 'not', 'or', 'repeat', 'return', 'then', 'true', 'until', 'while'}

def qstr(s):
    if s == '':
        return '""'
    out = ['"']
    for ch in s:
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\r':
            out.append('\\r')
        elif ch == '\t':
            out.append('\\t')
        elif 32 <= ord(ch) < 127:
            out.append(ch)
        else:
            b = ord(ch) & 255
            out.append('\\%d' % b)
    out.append('"')
    return ''.join(out)

def identok(s):
    return bool(re.match('^[A-Za-z_]\\w*$', s or '')) and s not in keywords

def walksyms(x, out):
    if isinstance(x, lsym):
        out.append(x)
        for y in x.a:
            walksyms(y, out)
            if isinstance(y, tuple):
                for z in y:
                    walksyms(z, out)
    elif isinstance(x, tuple):
        for y in x:
            walksyms(y, out)

class emitter2:

    def __init__(self, lifter, pid, upvresolver=None):
        self.curdefs = None
        self.lifter = lifter
        self.pid = pid
        self.pfx = 'p%d' % pid
        self.upvresolver = upvresolver
        self.rn = {}
        self.spill = None
        self.rptab = 'rp' + self.pfx
        self.un = {}
        self.tmp = 0
        self.packs = {}
        self.declaredpacks = set()
        self.linematerialized = {}
        self.callnames = {}
        self.va = None

    def regname(self, n):
        if n not in self.rn:
            if self.spill is not None and n >= self.spill:
                return '%s[%d]' % (self.rptab, n)
            self.rn[n] = 'v%s_%d' % (self.pfx, n)
        return self.rn[n]

    def bindreg(self, n, name):
        self.rn[n] = name

    def upvname(self, k):
        if k not in self.un:
            if self.upvresolver is not None:
                self.un[k] = self.upvresolver(k)
            else:
                self.un[k] = 'uv%s_%d' % (self.pfx, k)
        return self.un[k]

    def newtmp(self, pfx='t'):
        self.tmp += 1
        return '%s%s_%d' % (pfx, self.pfx, self.tmp)

    def ensureva(self):
        if self.va is None:
            self.va = 'va' + self.pfx
        return self.va

    def expr(self, s):
        if isinstance(s, lsym):
            m = getattr(self, 'x' + s.t.replace('_', ''), None)
            if m is None:
                return 'nil -- ?%s' % s.t
            return m(s)
        if s is None:
            return 'nil'
        if s is True:
            return 'true'
        if s is False:
            return 'false'
        if isinstance(s, (int, float)):
            return repr(s)
        if isinstance(s, str):
            return qstr(s)
        return repr(s)

    def xconst(self, s):
        v = s.a[0]
        if v is None:
            return 'nil'
        if v is True:
            return 'true'
        if v is False:
            return 'false'
        if isinstance(v, (int, float)):
            return repr(v)
        if isinstance(v, str):
            return qstr(v)
        return repr(v)

    def xreg(self, s):
        return self.regname(s.a[0])

    def xupv(self, s):
        return self.upvname(s.a[0])

    def xglob(self, s):
        g = s.a[0]
        if identok(g):
            return '_G.' + g
        return '_G[%s]' % qstr(g)

    def xindex(self, s):
        obj, key = (s.a[0], s.a[1])
        o = self.expr(obj)
        if isinstance(key, lsym) and key.t == 'const' and isinstance(key.a[0], str) and identok(key.a[0]):
            return '%s.%s' % (o, key.a[0])
        return '%s[%s]' % (o, self.expr(key))

    def xand(self, s):
        return '(%s and %s)' % (self.expr(s.a[0]), self.expr(s.a[1]))

    def xor2(self, s):
        return '(%s or %s)' % (self.expr(s.a[0]), self.expr(s.a[1]))

    def xnot(self, s):
        return '(not %s)' % self.expr(s.a[0])

    def xcmp(self, s):
        return '(%s %s %s)' % (self.expr(s.a[1]), s.a[0], self.expr(s.a[2]))

    def xarith(self, s):
        op = s.a[0]
        if op == '^':
            return '(%s^%s)' % (self.expr(s.a[1]), self.expr(s.a[2]))
        return '(%s %s %s)' % (self.expr(s.a[1]), op, self.expr(s.a[2]))

    def xconcat(self, s):
        b, c = s.a
        return '..'.join((self.regname(r) for r in range(b, c + 1)))

    def xlen(self, s):
        inner = self.expr(s.a[0])
        if isinstance(s.a[0], lsym) and s.a[0].t in ('and', 'or', 'cmp', 'arith', 'concat'):
            inner = '(' + inner + ')'
        return '#' + inner

    def xtype(self, s):
        return 'type(%s)' % self.expr(s.a[0])

    def xclosure(self, s):
        idx = s.a[0]
        return self.lifter.closuretext(idx, self)

    def xlib(self, s):
        a = s.a[0]
        return self.lifter.loadlibname(a)

    def xvararg(self, s):
        return '(...)'

    def xvarargn(self, s):
        va = self.ensureva()
        return '%s.n' % va

    def xregstop(self, s):
        base = s.a[0]
        d = getattr(self, 'curdefs', None)
        if d is not None and 0 <= base < len(d) and (d[base] is not None):
            if d[base].kind == 'pack':
                pk = self.packvar(d[base].src)
                return 'table.unpack(%s, 1, %s.n)' % (pk, pk)
            if d[base].kind == 'va':
                va = self.ensureva()
                return 'table.unpack(%s, 1, %s.n)' % (va, va)
            if d[base].kind == 'sym':
                parts = []
                i = base
                while i < len(d) and d[i] is not None and (d[i].kind == 'sym'):
                    parts.append(self.regname(i))
                    i += 1
                if i < len(d) and d[i] is not None and (d[i].kind == 'pack'):
                    pk = self.packvar(d[i].src)
                    parts.append('table.unpack(%s, 1, %s.n)' % (pk, pk))
                    return ', '.join(parts)
                if i < len(d) and d[i] is not None and (d[i].kind == 'va'):
                    va = self.ensureva()
                    parts.append('table.unpack(%s, 1, %s.n)' % (va, va))
                    return ', '.join(parts)
        return 'table.unpack(TOPMARK_%d)' % base

    def xvarargidx(self, s):
        va = self.ensureva()
        return '%s[%s]' % (va, self.expr(s.a[0]))
    xindexvararg = xvarargidx

    def xtablelit(self, s):
        items = s.a[0]
        parts = []
        for k, v in items:
            if isinstance(k, str) and identok(k):
                key = k
            elif isinstance(k, str):
                key = '[%s]' % qstr(k)
            else:
                key = '[%s]' % self.expr(k if isinstance(k, lsym) else S('const', k))
            vv = self.expr(v if isinstance(v, lsym) else S('const', v))
            parts.append('%s = %s' % (key, vv))
        return '{%s}' % ', '.join(parts)

    def xnewtable(self, s):
        return '{}'

    def xsetm(self, s):
        return 'nil -- setm?'

    def calltext(self, call):
        key = id(call)
        if key not in self.callnames:
            fn = self.expr(call.a[0])
            args = []
            for a in call.a[1]:
                if isinstance(a, lsym) and a.t == 'regs':
                    b, c = a.a
                    for r in range(b, c + 1):
                        args.append(self.regname(r))
                else:
                    args.append(self.expr(a))
            self.callnames[key] = '%s(%s)' % (fn, ', '.join(args))
        return self.callnames[key]

    def calltextwithargs(self, call, argoverride):
        fn = self.expr(call.a[0])
        args = []
        i = 0
        for a in call.a[1]:
            if isinstance(a, lsym) and a.t == 'regs':
                b, c = a.a
                for r in range(b, c + 1):
                    args.append(argoverride(i, self.regname(r)))
                    i += 1
            else:
                args.append(argoverride(i, self.expr(a)))
                i += 1
        return '%s(%s)' % (fn, ', '.join(args))

    def xcall(self, s):
        return self.calltext(s)

    def xcallres(self, s):
        call, idx = s.a
        pk = self.packvar(call)
        return '%s[%d]' % (pk, idx + 1)

    def xpackn(self, s):
        inner = s.a[0]
        if isinstance(inner, lsym) and inner.t == 'call':
            pk = self.packvar(inner)
            return '%s.n' % pk
        return "select('#', %s)" % self.expr(inner)

    def packvar(self, call):
        key = id(call)
        if key not in self.packs:
            self.packs[key] = self.newtmp('pk')
        return self.packs[key]
