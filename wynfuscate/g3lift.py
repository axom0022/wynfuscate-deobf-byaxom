from __future__ import annotations
import re


def luaq(s):
    out = s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '')
    return '"' + out + '"'


def ident(s):
    return bool(re.fullmatch(r'[A-Za-z_]\w*', s or '')) and not re.fullmatch(
        '(and|break|do|else|elseif|end|false|for|function|if|in|local|nil|not|or|repeat|return|then|true|until|while)', s)


def numtext(n):
    if isinstance(n, float) and n == int(n) and abs(n) < 1e15:
        return str(int(n))
    return repr(n)


class ctx:
    def __init__(self, lifter, P, regs, upnames):
        self.lf = lifter
        self.P = P
        self.rn = dict(regs)
        self.upnames = dict(upnames)
        self.tmp = 0
        self.lines = lifter.lines[P['pid']]

    def regname(self, r):
        if r not in self.rn:
            self.rn[r] = 'v%d' % r
        return self.rn[r]


class g3lifter:

    def __init__(self, vm, sem):
        self.vm = vm
        self.sem = sem
        self.lines = {}
        self.children = {}
        for P in vm.protos:
            self.prep(P)

    def unkcond(self, cond):
        def hasunk(v):
            if not isinstance(v, tuple):
                return False
            if v[0] == 'unk':
                return True
            if v[0] in ('reg', 'upv', 'global', 'num', 'str', 'bool', 'nil'):
                return False
            return any(hasunk(x) for x in v[1:] if isinstance(x, tuple))
        return hasunk(cond)

    def flatten(self, eff, out, c):
        for e in eff:
            k = e[0]
            if k == 'guard':
                inner = []
                self.flatten(e[2], inner, c)
                if not inner:
                    continue
                if self.unkcond(e[1]):
                    out.extend(inner)
                else:
                    out.append(('ifstmt', e[1], inner, []))
            elif k == 'alt':
                th, el = [], []
                self.flatten(e[2], th, c)
                self.flatten(e[3], el, c)
                cond = e[1]
                if not th and not el:
                    continue
                if self.unkcond(cond):
                    out.extend(th or el)
                    continue
                if len(th) == 1 and len(el) == 1 and th[0][0] == 'set' and el[0][0] == 'set' \
                        and th[0][1] == el[0][1]:
                    dst = th[0][1]
                    tv, ev = th[0][2], el[0][2]
                    if ev == cond:
                        out.append(('set', dst, ('bin', 'and', cond, tv)))
                        continue
                    if tv == cond:
                        out.append(('set', dst, ('bin', 'or', cond, ev)))
                        continue
                    if ev == ('nil',) and tv[0] == 'getf' and tv[1] == cond:
                        out.append(('set', dst, ('bin', 'and', cond, tv)))
                        continue
                if th and not el:
                    out.append(('ifstmt', cond, th, []))
                elif not th and el:
                    out.append(('ifstmt', ('un', 'not', cond), el, []))
                else:
                    out.append(('ifstmt', cond, th, el))
            elif k == 'setreg':
                out.append(('set', e[1], e[2]))
            elif k == 'setfield':
                out.append(('setf', e[1], e[2], e[3]))
            elif k == 'setglobal':
                nm = e[1]
                if isinstance(nm, tuple) and nm[0] == 'str':
                    nm = nm[1]
                out.append(('setg', nm, e[2]))
            elif k == 'setupval':
                out.append(('setu', e[1], e[2]))
            elif k == 'jump':
                out.append(('jump', e[1]))
            elif k == 'cjump':
                out.append(('cjump', e[1], e[2]))
            elif k == 'return':
                out.append(('return', e[1], e[2], e[3]))
            elif k == 'callmulti':
                out.append(('multi', e[2], e[1]))
            elif k == 'vararg-prep':
                out.append(('vprep', e[1]))
            elif k == 'vararg-use':
                out.append(('vuse', e[1], e[2]))
            elif k == 'closure':
                out.append(('closure', e[1], e[2]))
                c.append((e[2]))
            elif k == 'callstat':
                out.append(('callstat', e[1], e[2]))
            elif k == 'newtbl':
                out.append(('new', e[1], e[2]))
            elif k == 'concat':
                out.append(('concat', e[1], e[2], e[3]))
            elif k == 'close':
                pass
        return out

    def prep(self, P):
        pid = P['pid']
        lines = {}
        children = []
        n = P['n']
        for pc in range(1, n + 1):
            eff = self.sem.decode(P, pc)
            flat = []
            self.flatten(eff, flat, children)
            L = {'stmts': [], 'cjump': None, 'jump': None, 'ret': None}
            for e in flat:
                k = e[0]
                if k == 'set':
                    L['stmts'].append(e)
                elif k == 'setf':
                    L['stmts'].append(e)
                elif k == 'setg':
                    L['stmts'].append(e)
                elif k == 'setu':
                    L['stmts'].append(e)
                elif k == 'jump':
                    L['jump'] = e[1]
                elif k == 'cjump':
                    L['cjump'] = (e[1], e[2])
                elif k == 'return':
                    L['ret'] = (e[1], e[2], e[3])
                elif k == 'multi':
                    L['stmts'].append(('multi', e[1], e[2]))
                elif k == 'vprep':
                    L['stmts'].append(e)
                elif k == 'vuse':
                    L['stmts'].append(e)
                elif k == 'closure':
                    L['stmts'].append(e)
                elif k == 'new':
                    L['stmts'].append(e)
                elif k == 'callstat':
                    L['stmts'].append(e)
                elif k == 'concat':
                    L['stmts'].append(e)
                elif k == 'ifstmt':
                    L['stmts'].append(e)
            lines[pc] = L
        self.lines[pid] = lines
        self.children[pid] = children

    def analyze(self, lines, n):
        reach = {1}
        stack = [1]
        while stack:
            pc = stack.pop()
            if pc < 1 or pc > n or pc not in lines:
                continue
            L = lines[pc]
            succ = []
            if L['ret'] is not None:
                pass
            elif L['cjump'] is not None:
                succ = [pc + 1, L['cjump'][1]]
            elif L['jump'] is not None:
                succ = [L['jump']]
            else:
                succ = [pc + 1]
            for s2 in succ:
                if s2 not in reach and 1 <= s2 <= n:
                    reach.add(s2)
                    stack.append(s2)
        back = {}
        for pc in reach:
            L = lines[pc]
            tgts = []
            if L['cjump'] is not None:
                tgts.append(L['cjump'][1])
            if L['jump'] is not None:
                tgts.append(L['jump'])
            for t in tgts:
                if t < pc:
                    back.setdefault(t, []).append(pc)
        return reach, back

    def structure(self, pid, lo, hi, c, loopstack, depth=0):
        lines = self.lines[pid]
        n = c.P['n']
        reach, back = self.analyze(lines, n)
        out = []
        pc = lo
        while pc <= hi:
            if pc not in reach or pc not in lines:
                pc += 1
                continue
            L = lines[pc]
            if pc in back and depth < 40:
                tails = [t for t in back[pc] if lo <= t <= hi]
                if tails:
                    tail = max(tails)
                    out.extend(self.emitloop(pid, pc, tail, c, loopstack, depth))
                    pc = tail + 1
                    continue
            if L['cjump'] is not None:
                cond, t = L['cjump']
                if t == pc + 1 or t == pc:
                    out.extend(self.emitline(L, pc, c))
                    pc += 1
                    continue
                if t == hi + 1:
                    body = self.structure(pid, pc + 1, hi, c, loopstack, depth + 1)
                    out.append('if %s then' % self.valtext(('un', 'not', cond), c))
                    out.extend(('  ' + x for x in body))
                    out.append('end')
                    pc = hi + 1
                    continue
                if t > hi:
                    out.extend(self.emitline(L, pc, c))
                    if loopstack and t == loopstack[-1][1]:
                        out.append('if %s then break end' % self.valtext(cond, c))
                    else:
                        out.append('-- jump %d -> %d unstructured' % (pc, t))
                    pc += 1
                    continue
                elsejump = None
                M = lines.get(t - 1)
                if M is not None and M['jump'] is not None and M['jump'] > t \
                        and not M['stmts'] and M['cjump'] is None and M['ret'] is None:
                    elsejump = M['jump']
                if elsejump is not None and elsejump <= hi + 1:
                    thenbody = self.structure(pid, t, elsejump - 1, c, loopstack, depth + 1)
                    elsebody = self.structure(pid, pc + 1, t - 2, c, loopstack, depth + 1)
                    out.append('if %s then' % self.valtext(('un', 'not', cond), c))
                    out.extend(('  ' + x for x in thenbody))
                    if elsebody:
                        out.append('else')
                        out.extend(('  ' + x for x in elsebody))
                    out.append('end')
                    pc = elsejump
                else:
                    body = self.structure(pid, pc + 1, t - 1, c, loopstack, depth + 1)
                    out.append('if %s then' % self.valtext(('un', 'not', cond), c))
                    out.extend(('  ' + x for x in body))
                    out.append('end')
                    pc = t
                continue
            if L['jump'] is not None and not L['stmts'] and L['ret'] is None:
                t = L['jump']
                if t == pc + 1:
                    pc += 1
                    continue
                if t < pc:
                    pc += 1
                    continue
                if t > hi:
                    if loopstack and t == loopstack[-1][1]:
                        out.append('break')
                    pc += 1
                    continue
                pc = t
                continue
            out.extend(self.emitline(L, pc, c))
            pc += 1
        return out

    def emitloop(self, pid, head, tail, c, loopstack, depth):
        lines = self.lines[pid]
        out = []
        inner = self.structure(pid, head, tail - 1, c, loopstack + [(head, tail + 1)], depth + 1)
        T = lines.get(tail)
        condtxt = None
        if T is not None and T['cjump'] is not None:
            cond, t = T['cjump']
            if t == head:
                condtxt = self.valtext(('un', 'not', cond), c)
                tailstmts = []
            else:
                condtxt = None
                tailstmts = self.emitline(T, tail, c)
        elif T is not None and T['jump'] == head and not T['stmts']:
            tailstmts = []
        else:
            tailstmts = self.emitline(T, tail, c) if T is not None else []
        if condtxt is not None:
            out.append('while %s do' % condtxt)
        else:
            out.append('while true do')
            if T is not None and T['cjump'] is not None and T['cjump'][1] != head:
                cond, t = T['cjump']
                inner.append('if %s then break end' % self.valtext(('un', 'not', cond), c)
                             if t == tail + 1 else '-- odd tail jump %d -> %d' % (tail, t))
        out.extend(('  ' + x for x in inner))
        out.extend(('  ' + x for x in tailstmts))
        out.append('end')
        return out

    def emitline(self, L, pc, c):
        out = []
        for st in L['stmts']:
            out.extend(self.emitstmt(st, pc, c))
        if L['ret'] is not None:
            mode, a, b = L['ret']
            if mode == 'none':
                out.append('return')
            elif mode == 'varargs':
                out.append('return ...')
            elif mode == 'range' and a is not None:
                names = [c.regname(a + i) for i in range(0, (b - a + 1) if isinstance(b, int) else 1)]
                out.append('return ' + ', '.join(names))
            elif mode == 'call':
                out.append('return ' + self.valtext(a, c))
            else:
                out.append('return')
        return out

    def emitstmt(self, st, pc, c):
        k = st[0]
        if k == 'ifstmt':
            out = ['if %s then' % self.valtext(st[1], c)]
            for st2 in st[2]:
                out.extend(('  ' + x for x in self.emitstmt(st2, pc, c)))
            if st[3]:
                out.append('else')
                for st2 in st[3]:
                    out.extend(('  ' + x for x in self.emitstmt(st2, pc, c)))
            out.append('end')
            return out
        if k == 'callstat':
            ft = self.valtext(st[1], c)
            if ft in ('nil', 'true', 'false'):
                ft = '(' + ft + ')'
            return ['%s(%s)' % (ft, self.callargs(('call', st[1], st[2]), pc, c))]
        if k == 'concat':
            _, dst, lo, hi = st
            names = [c.regname(lo + i) for i in range(max(0, hi - lo + 1))]
            return ['%s = %s' % (c.regname(dst), ' .. '.join(names))]
        if k == 'set':
            dst, v = st[1], st[2]
            if v == ('reg', dst):
                return []
            if isinstance(v, tuple) and v[0] == 'closure':
                return self.emitclosure(dst, v[1], c)
            return ['%s = %s' % (c.regname(dst), self.valtext(v, c))]
        if k == 'setf':
            base, key, v = st[1], st[2], st[3]
            bt = self.valtext(base, c)
            if key[0] == 'str' and ident(key[1]):
                lhs = '%s.%s' % (bt, key[1])
            else:
                lhs = '%s[%s]' % (bt, self.valtext(key, c))
            return ['%s = %s' % (lhs, self.valtext(v, c))]
        if k == 'setg':
            name, v = st[1], st[2]
            if ident(str(name)):
                return ['%s = %s' % (name, self.valtext(v, c))]
            return ['_G[%s] = %s' % (luaq(str(name)), self.valtext(v, c))]
        if k == 'setu':
            i, v = st[1], st[2]
            nm = c.upnames.get(i, 'u%d' % i)
            return ['%s = %s' % (nm, self.valtext(v, c))]
        if k == 'multi':
            base, call = st[1], st[2]
            args = self.callargs(call, pc, c)
            ft = self.valtext(call[1], c)
            if ft in ('nil', 'true', 'false'):
                ft = '(' + ft + ')'
            return ['%s = %s' % (c.regname(base), '%s(%s)' % (ft, args))]
        if k == 'vprep':
            return []
        if k == 'vuse':
            base, n = st[1], st[2]
            if n in (0, 1):
                return ['%s = ...' % c.regname(base)]
            return [', '.join(c.regname(base + i) for i in range(n)) + ' = ...']
        if k == 'closure':
            dst, pid = st[1], st[2]
            return self.emitclosure(dst, pid, c)
        if k == 'new':
            dst, tmpl = st[1], st[2]
            return ['%s = {}' % c.regname(dst)]
        return []

    def callargs(self, call, pc, c):
        if call[0] == 'callres':
            call = call[1]
        if call[0] != 'call' or len(call) < 3:
            return ''
        f, args = call[1], call[2]
        parts = []
        for a in args:
            if a[0] == 'range':
                lo = a[1]
                hi = a[2]
                if hi == 'top':
                    parts.append('...')
                elif isinstance(hi, int):
                    parts.extend(c.regname(lo + i) for i in range(hi - lo + 1))
                else:
                    parts.append(c.regname(lo))
            else:
                parts.append(self.valtext(a, c))
        return ', '.join(parts)

    def emitclosure(self, dst, pid, c):
        pr = None
        for Q in self.vm.protos:
            if Q['pid'] == pid:
                pr = Q
                break
        if pr is None:
            return ['%s = nil -- missing proto %d' % (c.regname(dst), pid)]
        upnames = {}
        for i, (we, ez) in enumerate(pr['upvals']):
            if we:
                upnames[i] = c.regname(ez)
            else:
                upnames[i] = c.upnames.get(ez, 'u%d' % ez)
        params = []
        for i in range(pr['numparams']):
            params.append('v%d' % i)
        if pr['is_vararg']:
            params.append('...')
        c2 = ctx(self, pr, {i: 'v%d' % i for i in range(pr['numparams'])}, upnames)
        body = self.structure(pid, 1, pr['n'], c2, [], 0)
        head = '%s = function(%s)' % (c.regname(dst), ', '.join(params))
        out = [head]
        out.extend(('  ' + x for x in body))
        out.append('end')
        return out

    def valtext(self, v, c):
        k = v[0]
        if k == 'num':
            return numtext(v[1])
        if k == 'str':
            return luaq(v[1])
        if k == 'bool':
            return 'true' if v[1] else 'false'
        if k == 'nil':
            return 'nil'
        if k == 'reg':
            return c.regname(v[1])
        if k == 'upv':
            return c.upnames.get(v[1] - 1, 'u%d' % (v[1] - 1))
        if k == 'global':
            g = v[1]
            return g if ident(g) else '_G[%s]' % luaq(str(g))
        if k == 'getf':
            base, key = v[1], v[2]
            bt = self.valtext(base, c)
            if bt in ('nil', 'true', 'false') or bt[:1].isdigit() or bt[:1] == '"':
                bt = '(' + bt + ')'
            if key[0] == 'str' and ident(key[1]):
                return '%s.%s' % (bt, key[1])
            return '%s[%s]' % (bt, self.valtext(key, c))
        if k == 'call':
            ft = self.valtext(v[1], c)
            if ft in ('nil', 'true', 'false'):
                ft = '(' + ft + ')'
            return '%s(%s)' % (ft, self.callargs(v, 0, c))
        if k == 'callres':
            return self.valtext(v[1], c)
        if k == 'bin':
            a, b = self.valtext(v[2], c), self.valtext(v[3], c)
            if v[1] in ('and', 'or'):
                return '%s %s %s' % (a, v[1], b)
            return '(%s %s %s)' % (a, v[1], b)
        if k == 'un':
            return 'not %s' % self.valtext(v[2], c)
        if k == 'newtbl':
            return '{}'
        if k == 'closure':
            return 'function() end -- proto %d' % v[1]
        if k == 'varargx':
            return '...'
        if k == 'stdlibcall':
            return '%s.%s' % (v[1], v[2])
        if k in ('cmp',):
            return '(%s %s %s)' % (self.valtext(v[2], c), v[1], self.valtext(v[3], c))
        return 'nil'

    def liftscript(self):
        pr = self.vm.protos[0]
        params = ['v%d' % i for i in range(pr['numparams'])]
        if pr['is_vararg']:
            params.append('...')
        c0 = ctx(self, pr, {i: 'v%d' % i for i in range(pr['numparams'])}, {})
        body = self.structure(0, 1, pr['n'], c0, [], 0)
        out = ['local main = function(%s)' % ', '.join(params)]
        out.extend(('  ' + x for x in body))
        out.append('end')
        out.append('main(...)')
        return '\n'.join(out) + '\n'
