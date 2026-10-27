from __future__ import annotations
import re
import sys
import re
import sys

class polisherror(Exception):
    pass
keywords = {'and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function', 'if', 'in', 'local', 'nil', 'not', 'or', 'repeat', 'return', 'then', 'true', 'until', 'while'}
numre = re.compile('0[xX][0-9a-fA-F]+|\\d+\\.?\\d*(?:[eE][+-]?\\d+)?|\\.\\d+(?:[eE][+-]?\\d+)?')
namere = re.compile('[A-Za-z_][A-Za-z0-9_]*')
sym2 = ('..', '==', '~=', '<=', '>=')
sym1 = set('+-*/%^#<>=(){}[];:,.')
escapes = {'a': '\x07', 'b': '\x08', 'f': '\x0c', 'n': '\n', 'r': '\r', 't': '\t', 'v': '\x0b', '\\': '\\', '"': '"', "'": "'"}

def tokenize(src):
    toks = []
    i, n = (0, len(src))
    while i < n:
        c = src[i]
        if c in ' \t\r\n':
            i += 1
            continue
        if c == '-' and i + 1 < n and (src[i + 1] == '-'):
            j = src.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isdigit() or (c == '.' and i + 1 < n and src[i + 1].isdigit()):
            m = numre.match(src, i)
            if not m:
                raise polisherror('bad number at %d' % i)
            toks.append(('num', m.group(0)))
            i = m.end()
            continue
        if c.isalpha() or c == '_':
            m = namere.match(src, i)
            w = m.group(0)
            toks.append(('kw', w) if w in keywords else ('name', w))
            i = m.end()
            continue
        if c in '"\'':
            val, i = lexstring(src, i)
            toks.append(('str', val))
            continue
        if src.startswith('...', i):
            toks.append(('sym', '...'))
            i += 3
            continue
        two = src[i:i + 2]
        if two in sym2:
            toks.append(('sym', two))
            i += 2
            continue
        if c in sym1:
            toks.append(('sym', c))
            i += 1
            continue
        raise polisherror('bad char %r at offset %d' % (c, i))
    toks.append(('eof', ''))
    return toks

def lexstring(src, i):
    q = src[i]
    i += 1
    out = []
    n = len(src)
    while True:
        if i >= n:
            raise polisherror('unterminated string')
        c = src[i]
        if c == q:
            return (''.join(out), i + 1)
        if c == '\\':
            i += 1
            if i >= n:
                raise polisherror('bad escape')
            e = src[i]
            if e in escapes:
                out.append(escapes[e])
                i += 1
            elif e == '\n':
                i += 1
            elif e.isdigit():
                j = i
                while j < n and j < i + 3 and src[j].isdigit():
                    j += 1
                out.append(chr(int(src[i:j])))
                i = j
            elif e == 'x':
                out.append(chr(int(src[i + 1:i + 3], 16)))
                i += 3
            elif e == 'z':
                i += 1
                while i < n and src[i] in ' \t\r\n':
                    i += 1
            else:
                raise polisherror('bad escape \\%s' % e)
            continue
        out.append(c)
        i += 1
binprec = {'or': 1, 'and': 2, '==': 3, '~=': 3, '<': 3, '<=': 3, '>': 3, '>=': 3, '..': 4, '+': 5, '-': 5, '*': 6, '/': 6, '%': 6, '^': 8}
rightassoc = {'..', '^'}
unaryprec = 7

class parser:
    blockend = ('end', 'else', 'elseif', 'until')

    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def pk(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else self.t[-1]

    def nx(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def acc(self, kind, val=None):
        tk = self.pk()
        if tk[0] == kind and (val is None or tk[1] == val):
            self.i += 1
            return tk
        return None

    def exp(self, kind, val=None):
        tk = self.nx()
        if tk[0] != kind or (val is not None and tk[1] != val):
            raise polisherror('expected %s %r, got %r' % (kind, val, tk))
        return tk

    def chunk(self):
        b = self.block()
        if self.pk()[0] != 'eof':
            raise polisherror('trailing tokens %r' % (self.pk(),))
        return b

    def block(self):
        sts = []
        while True:
            tk = self.pk()
            if tk[0] == 'eof':
                break
            if tk[0] == 'kw' and tk[1] in self.blockend:
                break
            if tk[0] == 'kw' and tk[1] == 'return':
                self.nx()
                es = []
                if self.startsexpr():
                    es = self.explist()
                self.acc('sym', ';')
                sts.append(['return', es])
                break
            if tk[0] == 'kw' and tk[1] == 'break':
                self.nx()
                self.acc('sym', ';')
                sts.append(['break'])
                break
            s = self.stat()
            if s is not None:
                sts.append(s)
        return sts

    def startsexpr(self):
        tk = self.pk()
        if tk[0] in ('name', 'num', 'str'):
            return True
        if tk[0] == 'kw':
            return tk[1] in ('nil', 'true', 'false', 'function', 'not')
        if tk[0] == 'sym':
            return tk[1] in ('(', '{', '...', '-', '#')
        return False

    def stat(self):
        tk = self.pk()
        if tk == ('sym', ';'):
            self.nx()
            return None
        if tk[0] == 'kw':
            w = tk[1]
            if w == 'local':
                self.nx()
                if self.pk() == ('kw', 'function'):
                    raise polisherror('local function not supported')
                names = [self.exp('name')[1]]
                while self.acc('sym', ','):
                    names.append(self.exp('name')[1])
                es = []
                if self.acc('sym', '='):
                    es = self.explist()
                return ['local', names, es]
            if w == 'if':
                self.nx()
                branches = []
                c = self.expr()
                self.exp('kw', 'then')
                branches.append([c, self.block()])
                while self.pk() == ('kw', 'elseif'):
                    self.nx()
                    c = self.expr()
                    self.exp('kw', 'then')
                    branches.append([c, self.block()])
                els = None
                if self.acc('kw', 'else'):
                    els = self.block()
                self.exp('kw', 'end')
                return ['if', branches, els]
            if w == 'while':
                self.nx()
                c = self.expr()
                self.exp('kw', 'do')
                b = self.block()
                self.exp('kw', 'end')
                return ['while', c, b]
            if w == 'repeat':
                self.nx()
                b = self.block()
                self.exp('kw', 'until')
                c = self.expr()
                return ['repeat', b, c]
            if w == 'for':
                self.nx()
                n1 = self.exp('name')[1]
                if self.acc('sym', '='):
                    e1 = self.expr()
                    self.exp('sym', ',')
                    e2 = self.expr()
                    e3 = None
                    if self.acc('sym', ','):
                        e3 = self.expr()
                    self.exp('kw', 'do')
                    b = self.block()
                    self.exp('kw', 'end')
                    return ['fornum', n1, e1, e2, e3, b]
                names = [n1]
                while self.acc('sym', ','):
                    names.append(self.exp('name')[1])
                self.exp('kw', 'in')
                es = self.explist()
                self.exp('kw', 'do')
                b = self.block()
                self.exp('kw', 'end')
                return ['forin', names, es, b]
            if w == 'do':
                self.nx()
                b = self.block()
                self.exp('kw', 'end')
                return ['do', b]
            raise polisherror('unexpected keyword %r' % w)
        e = self.suffixed()
        if self.pk() == ('sym', ',') or self.pk() == ('sym', '='):
            targets = [e]
            while self.acc('sym', ','):
                targets.append(self.suffixed())
            for t in targets:
                if t[0] not in ('name', 'index'):
                    raise polisherror('bad assignment target')
            self.exp('sym', '=')
            es = self.explist()
            return ['assign', targets, es]
        if e[0] in ('call', 'method'):
            return ['callstat', e]
        raise polisherror('expression statement is not a call')

    def explist(self):
        es = [self.expr()]
        while self.acc('sym', ','):
            es.append(self.expr())
        return es

    def expr(self, minp=0):
        tk = self.pk()
        if tk == ('kw', 'not'):
            self.nx()
            left = ['unop', 'not', self.expr(unaryprec)]
        elif tk == ('sym', '-'):
            self.nx()
            left = ['unop', '-', self.expr(unaryprec)]
        elif tk == ('sym', '#'):
            self.nx()
            left = ['unop', '#', self.expr(unaryprec)]
        else:
            left = self.suffixed()
        while True:
            tk = self.pk()
            op = None
            if tk[0] == 'kw' and tk[1] in ('and', 'or'):
                op = tk[1]
            elif tk[0] == 'sym' and tk[1] in binprec:
                op = tk[1]
            if op is None:
                break
            p = binprec[op]
            if p < minp:
                break
            self.nx()
            nxt = p if op in rightassoc else p + 1
            left = ['binop', op, left, self.expr(nxt)]
        return left

    def suffixed(self):
        e = self.primary()
        while True:
            tk = self.pk()
            if tk == ('sym', '.'):
                self.nx()
                nm = self.exp('name')[1]
                e = ['index', e, ['str', nm]]
            elif tk == ('sym', '['):
                self.nx()
                k = self.expr()
                self.exp('sym', ']')
                e = ['index', e, k]
            elif tk == ('sym', '('):
                e = ['call', e, self.arglist()]
            elif tk == ('sym', '{'):
                e = ['call', e, [self.table()]]
            elif tk[0] == 'str':
                self.nx()
                e = ['call', e, [['str', tk[1]]]]
            elif tk == ('sym', ':'):
                self.nx()
                nm = self.exp('name')[1]
                if self.pk() == ('sym', '('):
                    args = self.arglist()
                elif self.pk()[0] == 'str':
                    args = [['str', self.nx()[1]]]
                elif self.pk() == ('sym', '{'):
                    args = [self.table()]
                else:
                    raise polisherror('bad method args')
                e = ['method', e, nm, args]
            else:
                break
        return e

    def arglist(self):
        self.exp('sym', '(')
        es = []
        if self.pk() != ('sym', ')'):
            es = self.explist()
        self.exp('sym', ')')
        return es

    def primary(self):
        tk = self.pk()
        if tk[0] == 'name':
            self.nx()
            return ['name', tk[1]]
        if tk[0] == 'num':
            self.nx()
            return ['num', tk[1]]
        if tk[0] == 'str':
            self.nx()
            return ['str', tk[1]]
        if tk == ('sym', '('):
            self.nx()
            e = self.expr()
            self.exp('sym', ')')
            return e
        if tk == ('sym', '{'):
            return self.table()
        if tk == ('kw', 'function'):
            self.nx()
            return self.funcbody()
        if tk[0] == 'kw' and tk[1] in ('nil', 'true', 'false'):
            self.nx()
            return [tk[1]]
        if tk == ('sym', '...'):
            self.nx()
            return ['vararg']
        raise polisherror('unexpected token %r' % (tk,))

    def funcbody(self):
        self.exp('sym', '(')
        params = []
        if self.pk() != ('sym', ')'):
            while True:
                if self.acc('sym', '...'):
                    params.append('...')
                    break
                params.append(self.exp('name')[1])
                if not self.acc('sym', ','):
                    break
        self.exp('sym', ')')
        b = self.block()
        self.exp('kw', 'end')
        return ['func', params, b]

    def table(self):
        self.exp('sym', '{')
        items = []
        if self.acc('sym', '}'):
            return ['table', items]
        while True:
            if self.pk() == ('sym', '}'):
                break
            if self.pk() == ('sym', '['):
                self.nx()
                k = self.expr()
                self.exp('sym', ']')
                self.exp('sym', '=')
                items.append([k, self.expr()])
            elif self.pk()[0] == 'name' and self.pk(1) == ('sym', '='):
                nm = self.nx()[1]
                self.nx()
                items.append([['str', nm], self.expr()])
            else:
                items.append([None, self.expr()])
            if not (self.acc('sym', ',') or self.acc('sym', ';')):
                break
        self.exp('sym', '}')
        return ['table', items]
renpat = re.compile('^(?:[vaikc]p\\d+_\\d+|slp\\d+_\\d+|tp\\d+_\\d+|uvp\\d+_\\d+|pkp\\d+_\\d+|vap\\d+|rpp\\d+)$')

def cp(e):
    k = e[0]
    if k in ('name', 'num', 'str', 'nil', 'true', 'false', 'vararg'):
        return list(e)
    if k == 'index':
        return ['index', cp(e[1]), cp(e[2])]
    if k == 'call':
        return ['call', cp(e[1]), [cp(a) for a in e[2]]]
    if k == 'method':
        return ['method', cp(e[1]), e[2], [cp(a) for a in e[3]]]
    if k == 'binop':
        return ['binop', e[1], cp(e[2]), cp(e[3])]
    if k == 'unop':
        return ['unop', e[1], cp(e[2])]
    if k == 'table':
        return ['table', [[cp(it[0]) if it[0] is not None else None, cp(it[1])] for it in e[1]]]
    if k == 'func':
        return e
    raise polisherror('cp: %s' % k)

def eqexpr(a, b):
    if a is b:
        return True
    if a[0] != b[0]:
        return False
    k = a[0]
    if k in ('name', 'num', 'str'):
        return a[1] == b[1]
    if k in ('nil', 'true', 'false', 'vararg'):
        return True
    if k == 'index':
        return eqexpr(a[1], b[1]) and eqexpr(a[2], b[2])
    if k == 'call':
        return eqexpr(a[1], b[1]) and len(a[2]) == len(b[2]) and all((eqexpr(x, y) for x, y in zip(a[2], b[2])))
    if k == 'method':
        return a[1:] == b[1:] or (eqexpr(a[1], b[1]) and a[2] == b[2] and (len(a[3]) == len(b[3])) and all((eqexpr(x, y) for x, y in zip(a[3], b[3]))))
    if k == 'binop':
        return a[1] == b[1] and eqexpr(a[2], b[2]) and eqexpr(a[3], b[3])
    if k == 'unop':
        return a[1] == b[1] and eqexpr(a[2], b[2])
    if k == 'table':
        if len(a[1]) != len(b[1]):
            return False
        for ia, ib in zip(a[1], b[1]):
            if (ia[0] is None) != (ib[0] is None):
                return False
            if ia[0] is not None and (not eqexpr(ia[0], ib[0])):
                return False
            if not eqexpr(ia[1], ib[1]):
                return False
        return True
    return False

def subblocks(st):
    k = st[0]
    if k == 'if':
        for br in st[1]:
            yield br[1]
        if st[2] is not None:
            yield st[2]
    elif k == 'while':
        yield st[2]
    elif k == 'repeat':
        yield st[1]
    elif k == 'fornum':
        yield st[5]
    elif k == 'forin':
        yield st[3]
    elif k == 'do':
        yield st[1]

def stmtexprlists(st):
    k = st[0]
    if k == 'local':
        return [st[2]]
    if k == 'assign':
        return [st[2], [t[1] for t in st[1] if t[0] == 'index'], [t[2] for t in st[1] if t[0] == 'index']]
    if k == 'callstat':
        return [[st[1]]]
    if k == 'return':
        return [st[1]]
    if k == 'if':
        return [[br[0] for br in st[1]]]
    if k == 'while':
        return [[st[1]]]
    if k == 'repeat':
        return [[st[2]]]
    if k == 'fornum':
        return [[st[2], st[3]] + ([st[4]] if st[4] is not None else [])]
    if k == 'forin':
        return [st[2]]
    return []

def funcsinexpr(e, out):
    k = e[0]
    if k == 'index':
        funcsinexpr(e[1], out)
        funcsinexpr(e[2], out)
    elif k == 'call':
        funcsinexpr(e[1], out)
        for a in e[2]:
            funcsinexpr(a, out)
    elif k == 'method':
        funcsinexpr(e[1], out)
        for a in e[3]:
            funcsinexpr(a, out)
    elif k == 'binop':
        funcsinexpr(e[2], out)
        funcsinexpr(e[3], out)
    elif k == 'unop':
        funcsinexpr(e[2], out)
    elif k == 'table':
        for it in e[1]:
            if it[0] is not None:
                funcsinexpr(it[0], out)
            funcsinexpr(it[1], out)
    elif k == 'func':
        out.append(e)

def funcsinstmt(st, out):
    for lst in stmtexprlists(st):
        for e in lst:
            funcsinexpr(e, out)
    for bl in subblocks(st):
        for s2 in bl:
            funcsinstmt(s2, out)

def hascall(e):
    k = e[0]
    if k in ('call', 'method'):
        return True
    if k == 'index':
        return hascall(e[1]) or hascall(e[2])
    if k == 'binop':
        return hascall(e[2]) or hascall(e[3])
    if k == 'unop':
        return hascall(e[2])
    if k == 'table':
        for it in e[1]:
            if it[0] is not None and hascall(it[0]):
                return True
            if hascall(it[1]):
                return True
        return False
    return False

def blockhascall(block):
    for st in block:
        for lst in stmtexprlists(st):
            for e in lst:
                if hascall(e):
                    return True
        for f in stmtfuncs(st):
            if blockhascall(f[2]):
                return True
        for bl in subblocks(st):
            if blockhascall(bl):
                return True
    return False

def stmtfuncs(st):
    out = []
    funcsinstmt(st, out)
    return out

def stmtwrites(st):
    k = st[0]
    if k == 'local':
        return set(st[1])
    if k == 'assign':
        return {t[1] for t in st[1] if t[0] == 'name'}
    if k == 'fornum':
        return {st[1]}
    if k == 'forin':
        return set(st[1])
    return set()

def blockwatches(block, watch):
    for st in block:
        if stmtwrites(st) & watch:
            return True
        for bl in subblocks(st):
            if blockwatches(bl, watch):
                return True
        for f in stmtfuncs(st):
            if blockwatches(f[2], watch):
                return True
    return False

def exprreads(e, out):
    k = e[0]
    if k == 'name':
        out.append(e[1])
    elif k == 'index':
        exprreads(e[1], out)
        exprreads(e[2], out)
    elif k == 'call':
        exprreads(e[1], out)
        for a in e[2]:
            exprreads(a, out)
    elif k == 'method':
        exprreads(e[1], out)
        for a in e[3]:
            exprreads(a, out)
    elif k == 'binop':
        exprreads(e[2], out)
        exprreads(e[3], out)
    elif k == 'unop':
        exprreads(e[2], out)
    elif k == 'func':
        for s2 in e[2]:
            stmtreads(s2, out)
    elif k == 'table':
        for it in e[1]:
            if it[0] is not None:
                exprreads(it[0], out)
            exprreads(it[1], out)

def stmtreads(st, out):
    k = st[0]
    if k == 'local':
        for e in st[2]:
            exprreads(e, out)
    elif k == 'assign':
        for t in st[1]:
            if t[0] == 'index':
                exprreads(t[1], out)
                exprreads(t[2], out)
        for e in st[2]:
            exprreads(e, out)
    elif k == 'callstat':
        exprreads(st[1], out)
    elif k == 'return':
        for e in st[1]:
            exprreads(e, out)
    elif k == 'if':
        for c, b in st[1]:
            exprreads(c, out)
            for s2 in b:
                stmtreads(s2, out)
        if st[2] is not None:
            for s2 in st[2]:
                stmtreads(s2, out)
    elif k == 'while':
        exprreads(st[1], out)
        for s2 in st[2]:
            stmtreads(s2, out)
    elif k == 'repeat':
        for s2 in st[1]:
            stmtreads(s2, out)
        exprreads(st[2], out)
    elif k == 'fornum':
        exprreads(st[2], out)
        exprreads(st[3], out)
        if st[4] is not None:
            exprreads(st[4], out)
        for s2 in st[5]:
            stmtreads(s2, out)
    elif k == 'forin':
        for e in st[2]:
            exprreads(e, out)
        for s2 in st[3]:
            stmtreads(s2, out)
    elif k == 'do':
        for s2 in st[1]:
            stmtreads(s2, out)

def collectlocals(block):
    out = []

    def walk(stmts):
        for st in stmts:
            k = st[0]
            if k == 'local':
                out.extend(st[1])
            elif k == 'fornum':
                out.append(st[1])
            elif k == 'forin':
                out.extend(st[1])
            for bl in subblocks(st):
                walk(bl)
    walk(block)
    return out

def collectallnames(block):
    locs, alln = (set(), set())

    def walk(stmts, own):
        for st in stmts:
            for n in stmtwrites(st):
                alln.add(n)
                locs.add(n)
            for lst in stmtexprlists(st):
                for e in lst:
                    namesinexpr(e, alln)
            for bl in subblocks(st):
                walk(bl, own)
            for f in stmtfuncs(st):
                walk(f[2], own)

    def namesinexpr(e, out):
        k = e[0]
        if k == 'name':
            out.add(e[1])
        elif k == 'index':
            namesinexpr(e[1], out)
            namesinexpr(e[2], out)
        elif k == 'call':
            namesinexpr(e[1], out)
            for a in e[2]:
                namesinexpr(a, out)
        elif k == 'method':
            namesinexpr(e[1], out)
            for a in e[3]:
                namesinexpr(a, out)
        elif k == 'binop':
            namesinexpr(e[2], out)
            namesinexpr(e[3], out)
        elif k == 'unop':
            namesinexpr(e[2], out)
        elif k == 'func':
            for i, p in enumerate(e[1]):
                out.add(p)
            walk(e[2], None)
        elif k == 'table':
            for it in e[1]:
                if it[0] is not None:
                    namesinexpr(it[0], out)
                namesinexpr(it[1], out)
    walk(block, None)
    return (locs, alln)

def closurewrittennames(block):
    cw = set()

    def visit(stmts, own):
        for st in stmts:
            cw.update(stmtwrites(st) - own)
            for bl in subblocks(st):
                visit(bl, own)
            for f in stmtfuncs(st):
                inner = {p for p in f[1] if p != '...'} | set(collectlocals(f[2]))
                visit(f[2], inner)
    topown = set(collectlocals(block))
    visit(block, topown)
    return cw

def mapexpr(e, fn):
    k = e[0]
    if k in ('name', 'num', 'str', 'nil', 'true', 'false', 'vararg'):
        return fn(e)
    if k == 'index':
        return fn(['index', mapexpr(e[1], fn), mapexpr(e[2], fn)])
    if k == 'call':
        return fn(['call', mapexpr(e[1], fn), [mapexpr(a, fn) for a in e[2]]])
    if k == 'method':
        return fn(['method', mapexpr(e[1], fn), e[2], [mapexpr(a, fn) for a in e[3]]])
    if k == 'binop':
        return fn(['binop', e[1], mapexpr(e[2], fn), mapexpr(e[3], fn)])
    if k == 'unop':
        return fn(['unop', e[1], mapexpr(e[2], fn)])
    if k == 'table':
        return fn(['table', [[mapexpr(it[0], fn) if it[0] is not None else None, mapexpr(it[1], fn)] for it in e[1]]])
    if k == 'func':
        return fn(e)
    raise polisherror('map_expr: %s' % k)

def valuerules(ch):

    def fn(e):
        if e[0] == 'unop' and e[1] == 'not':
            a = e[2]
            if a[0] == 'binop' and a[1] == '==':
                ch[0] = True
                return ['binop', '~=', a[2], a[3]]
            if a[0] == 'binop' and a[1] == '~=':
                ch[0] = True
                return ['binop', '==', a[2], a[3]]
            if a[0] == 'true':
                ch[0] = True
                return ['false']
            if a[0] == 'false':
                ch[0] = True
                return ['true']
            if a[0] == 'binop' and a[1] == 'and' and (a[2][0] == 'binop') and (a[2][1] == '~=') and (a[2][2][0] == 'name') and (a[2][3] == ['nil']) and eqexpr(a[3], a[2][2]):
                ch[0] = True
                return ['unop', 'not', a[3]]
        if e[0] == 'call' and e[1][0] == 'binop' and (e[1][1] == 'and'):
            A, B = (e[1][2], e[1][3])
            if B[0] == 'index' and B[2][0] == 'str' and eqexpr(B[1], A) and e[2] and eqexpr(e[2][0], A):
                ch[0] = True
                return ['method', A, B[2][1], e[2][1:]]
        return e
    return fn

def condrules(ch):
    base = valuerules(ch)

    def fn(e):
        e2 = base(e)
        if e2 is not e:
            return e2
        if e[0] == 'unop' and e[1] == 'not' and (e[2][0] == 'unop') and (e[2][1] == 'not'):
            ch[0] = True
            return e[2][2]
        if e[0] == 'binop' and e[1] == 'and' and (e[2][0] == 'binop') and (e[2][1] == '~=') and (e[2][2][0] == 'name') and (e[2][3] == ['nil']) and eqexpr(e[3], e[2][2]):
            ch[0] = True
            return e[3]
        return e
    return fn

def simplifyall(block):
    ch = [False]
    vfn = valuerules(ch)
    cfn = condrules(ch)

    def scan(stmts):
        for st in stmts:
            k = st[0]
            if k == 'local':
                st[2] = [mapexpr(e, vfn) for e in st[2]]
            elif k == 'assign':
                st[2] = [mapexpr(e, vfn) for e in st[2]]
                for t in st[1]:
                    if t[0] == 'index':
                        t[1] = mapexpr(t[1], vfn)
                        t[2] = mapexpr(t[2], vfn)
            elif k == 'callstat':
                st[1] = mapexpr(st[1], vfn)
            elif k == 'return':
                st[1] = [mapexpr(e, vfn) for e in st[1]]
            elif k == 'if':
                for br in st[1]:
                    br[0] = mapexpr(br[0], cfn)
            elif k == 'while':
                st[1] = mapexpr(st[1], cfn)
            elif k == 'repeat':
                st[2] = mapexpr(st[2], cfn)
            elif k == 'fornum':
                st[2] = mapexpr(st[2], vfn)
                st[3] = mapexpr(st[3], vfn)
                if st[4] is not None:
                    st[4] = mapexpr(st[4], vfn)
            elif k == 'forin':
                st[2] = [mapexpr(e, vfn) for e in st[2]]
            for bl in subblocks(st):
                scan(bl)
            for f in stmtfuncs(st):
                scan(f[2])
    scan(block)
    return ch[0]

class subst:
    __slots__ = ('x', 'rhs', 'haltcalls', 'halted', 'substed')

    def __init__(self, x, rhs, haltcalls):
        self.x = x
        self.rhs = rhs
        self.haltcalls = haltcalls
        self.halted = False
        self.substed = False

    def e(self, e):
        if self.halted:
            return e
        k = e[0]
        if k == 'name':
            if e[1] == self.x:
                self.substed = True
                return cp(self.rhs)
            return e
        if k in ('num', 'str', 'nil', 'true', 'false', 'vararg', 'func'):
            return e
        if k == 'index':
            e[1] = self.e(e[1])
            e[2] = self.e(e[2])
            return e
        if k == 'call':
            e[1] = self.e(e[1])
            e[2] = [self.e(a) for a in e[2]]
            if self.haltcalls:
                self.halted = True
            return e
        if k == 'method':
            e[1] = self.e(e[1])
            e[3] = [self.e(a) for a in e[3]]
            if self.haltcalls:
                self.halted = True
            return e
        if k == 'binop':
            e[2] = self.e(e[2])
            e[3] = self.e(e[3])
            return e
        if k == 'unop':
            e[2] = self.e(e[2])
            return e
        if k == 'table':
            e[1] = [[self.e(it[0]) if it[0] is not None else None, self.e(it[1])] for it in e[1]]
            return e
        raise polisherror('Subst.e: %s' % k)

def blockunreach(block):
    if not block:
        return False
    last = block[-1]
    if last[0] in ('return', 'break'):
        return True
    if last[0] == 'do':
        return blockunreach(last[1])
    if last[0] == 'if' and last[2] is not None:
        return all((blockunreach(b) for _, b in last[1])) and blockunreach(last[2])
    return False

def substblock(stmts, start, S):
    watch = {S.x} | ({S.rhs[1]} if S.rhs[0] == 'name' else set())
    writes = False
    for j in range(start, len(stmts)):
        w, unreach = subststmt(stmts[j], S, watch)
        if w:
            writes = True
        if w or unreach:
            break
    return writes

def subststmt(st, S, watch):
    k = st[0]
    if k == 'local':
        st[2] = [S.e(e) for e in st[2]]
        return (bool(watch & set(st[1])), False)
    if k == 'assign':
        st[2] = [S.e(e) for e in st[2]]
        for t in st[1]:
            if t[0] == 'index':
                t[1] = S.e(t[1])
                t[2] = S.e(t[2])
        return (bool(watch & {t[1] for t in st[1] if t[0] == 'name'}), False)
    if k == 'callstat':
        st[1] = S.e(st[1])
        return (False, False)
    if k == 'return':
        st[1] = [S.e(e) for e in st[1]]
        return (False, True)
    if k == 'break':
        return (False, True)
    if k == 'do':
        w = substblock(st[1], 0, S)
        return (w, blockunreach(st[1]))
    if k == 'if':
        wany = False
        for br in st[1]:
            br[0] = S.e(br[0])
            if substblock(br[1], 0, S):
                wany = True
        if st[2] is not None:
            if substblock(st[2], 0, S):
                wany = True
        return (wany, blockunreachstmtif(st))
    if k == 'while':
        if blockwatches(st[2], watch):
            return (True, False)
        if S.haltcalls and blockhascall(st[2]):
            return (True, False)
        st[1] = S.e(st[1])
        w = substblock(st[2], 0, S)
        return (w, False)
    if k == 'repeat':
        if blockwatches(st[1], watch):
            return (True, False)
        if S.haltcalls and blockhascall(st[1]):
            return (True, False)
        w = substblock(st[1], 0, S)
        st[2] = S.e(st[2])
        return (w, False)
    if k == 'fornum':
        st[2] = S.e(st[2])
        st[3] = S.e(st[3])
        if st[4] is not None:
            st[4] = S.e(st[4])
        if st[1] in watch or blockwatches(st[5], watch) or (S.haltcalls and blockhascall(st[5])):
            return (True, False)
        w = substblock(st[5], 0, S)
        return (w, False)
    if k == 'forin':
        st[2] = [S.e(e) for e in st[2]]
        if watch & set(st[1]) or blockwatches(st[3], watch) or (S.haltcalls and blockhascall(st[3])):
            return (True, False)
        w = substblock(st[3], 0, S)
        return (w, False)
    raise polisherror('subst_stmt: %s' % k)

def blockunreachstmtif(st):
    if st[2] is None:
        return False
    return all((blockunreach(b) for _, b in st[1])) and blockunreach(st[2])

def copypropall(block, cw, localnames):
    ch = [False]

    def scan(stmts):
        for i, st in enumerate(stmts):
            k = st[0]
            cand = None
            if k == 'assign' and len(st[1]) == 1 and (st[1][0][0] == 'name') and (len(st[2]) == 1):
                x, rhs = (st[1][0][1], st[2][0])
                if x in localnames:
                    cand = (x, rhs)
            elif k == 'local' and len(st[1]) == 1 and (len(st[2]) == 1):
                x, rhs = (st[1][0], st[2][0])
                cand = (x, rhs)
            if cand is not None:
                x, rhs = cand
                if rhs[0] in ('name', 'num', 'str', 'nil', 'true', 'false') and (not (rhs[0] == 'name' and rhs[1] == x)):
                    watch = {x} | ({rhs[1]} if rhs[0] == 'name' else set())
                    S = subst(x, rhs, bool(watch & cw))
                    substblock(stmts, i + 1, S)
                    ch[0] |= S.substed
            for bl in subblocks(st):
                scan(bl)
            for f in stmtfuncs(st):
                scan(f[2])
    scan(block)
    return ch[0]

def ispure(e):
    k = e[0]
    if k in ('name', 'num', 'str', 'nil', 'true', 'false'):
        return True
    if k == 'index':
        return e[1] == ['name', '_G'] and e[2][0] == 'str'
    if k == 'unop':
        if e[1] == 'not':
            return ispure(e[2])
        return e[2][0] == 'num'
    if k == 'binop':
        op, l, r = (e[1], e[2], e[3])
        if op in ('and', 'or'):
            return ispure(l) and ispure(r)
        if op in ('+', '-', '*', '/', '%', '^'):
            return l[0] == 'num' and r[0] == 'num'
        if op in '..':
            return l[0] == 'str' and r[0] == 'str'
        if op in ('==', '~='):
            lit = ('num', 'str', 'nil', 'true', 'false')
            return (l[0] in lit or r[0] in lit) and ispure(l) and ispure(r)
        return l[0] == 'num' and r[0] == 'num' or (l[0] == 'str' and r[0] == 'str')
    if k == 'table':
        return not e[1]
    if k == 'func':
        return True
    return False

def ismovable(e):
    k = e[0]
    if k in ('name', 'num', 'str', 'nil', 'true', 'false'):
        return True
    if k == 'index':
        return ismovable(e[1]) and e[2][0] == 'str'
    return False

def computeneedsbinding(block):
    nb = set()

    def visit(stmts):
        for st in stmts:
            r = []
            stmtreads(st, r)
            nb.update(r)
            k = st[0]
            if k == 'assign':
                plain = [t[1] for t in st[1] if t[0] == 'name']
                if plain and any((not ispure(e) and e[0] not in ('call', 'method') for e in st[2])):
                    nb.update(plain)
            for bl in subblocks(st):
                visit(bl)
            for f in stmtfuncs(st):
                visit(f[2])
    visit(block)
    return nb

def dceall(block):
    ch = [False]
    dceblock(block, set(), [], ch)
    return ch[0]

def dceblock(stmts, live, loopexit, ch):
    for j, st in enumerate(stmts):
        if st[0] in ('return', 'break') and j < len(stmts) - 1:
            del stmts[j + 1:]
            ch[0] = True
            break

    def uses(es):
        u = []
        for e in es:
            exprreads(e, u)
        return set(u)
    i = len(stmts) - 1
    while i >= 0:
        st = stmts[i]
        k = st[0]
        deleted = False
        if k == 'return':
            live = uses(st[1])
        elif k == 'break':
            live = set(loopexit[-1]) if loopexit else set()
        elif k == 'callstat':
            live |= uses([st[1]])
        elif k == 'local':
            names, es = (st[1], st[2])
            u = uses(es)
            orig = set(names)
            if not es:
                keep = [n for n in names if n in live or n in needsbind]
                if len(keep) != len(names):
                    ch[0] = True
                if not keep:
                    del stmts[i]
                    deleted = True
                else:
                    st[1] = keep
            elif len(es) == len(names):
                dropped = []
                while names and names[-1] not in live and (names[-1] not in needsbind) and (ispure(es[-1]) or es[-1][0] in ('call', 'method')):
                    nm = names.pop()
                    e = es.pop()
                    if e[0] in ('call', 'method'):
                        dropped.append(e)
                    ch[0] = True
                if names:
                    stmts[i + 1:i + 1] = [['callstat', e] for e in reversed(dropped)]
                elif dropped:
                    stmts[i:i + 1] = [['callstat', e] for e in reversed(dropped)]
                else:
                    del stmts[i]
                    deleted = True
            elif all((n not in live and n not in needsbind for n in names)) and len(es) == 1:
                e = es[0]
                if ispure(e):
                    del stmts[i]
                    deleted = True
                    ch[0] = True
                elif e[0] in ('call', 'method'):
                    stmts[i] = ['callstat', e]
                    ch[0] = True
            live = live - orig | u
        elif k == 'assign':
            targets, es = (st[1], st[2])
            u = []
            for t in targets:
                if t[0] == 'index':
                    exprreads(t[1], u)
                    exprreads(t[2], u)
            for e in es:
                exprreads(e, u)
            u = set(u)
            plain = [t for t in targets if t[0] == 'name']
            deadable = len(targets) == 1 and len(es) == 1 and plain and islocal(plain[0][1]) and (plain[0][1] not in live)
            if deadable:
                e = es[0]
                if ispure(e):
                    del stmts[i]
                    deleted = True
                    ch[0] = True
                elif e[0] in ('call', 'method'):
                    stmts[i] = ['callstat', e]
                    ch[0] = True
            live = live - {t[1] for t in plain} | u
        elif k == 'if':
            parts = []
            for c, b in st[1]:
                lb = dceblock(b, set(live), loopexit, ch)
                parts.append(lb | uses([c]))
            if st[2] is not None:
                parts.append(dceblock(st[2], set(live), loopexit, ch))
            else:
                parts.append(set(live))
            live = set().union(*parts) if parts else set(live)
        elif k == 'while':
            cur = set(live)
            for _ in range(4):
                nb = dceblock(st[2], set(cur), loopexit + [set(live)], ch)
                if nb <= cur:
                    break
                cur |= nb
            live = cur | uses([st[1]])
        elif k == 'repeat':
            cur = set(live)
            for _ in range(4):
                nb = dceblock(st[1], set(cur), loopexit + [set(live)], ch)
                if nb <= cur:
                    break
                cur |= nb
            live = cur | uses([st[2]])
        elif k == 'fornum':
            cur = set(live)
            for _ in range(4):
                nb = dceblock(st[5], set(cur), loopexit + [set(live)], ch)
                if nb <= cur:
                    break
                cur |= nb
            u = uses([st[2], st[3]] + ([st[4]] if st[4] is not None else []))
            live = cur - {st[1]} | u
        elif k == 'forin':
            cur = set(live)
            for _ in range(4):
                nb = dceblock(st[3], set(cur), loopexit + [set(live)], ch)
                if nb <= cur:
                    break
                cur |= nb
            live = cur - set(st[1]) | uses(st[2])
        elif k == 'do':
            live = dceblock(st[1], set(live), loopexit, ch)
        if not deleted:
            for f in stmtfuncs(st):
                own = {p for p in f[1] if p != '...'} | set(collectlocals(f[2]))
                dceblock(f[2], set(allreads) - own, [], ch)
                live |= allreadnames(f[2]) - own
        i -= 1
    return live
localnames2 = set()
needsbind = set()
allreads = set()

def allreadnames(block):
    out = []
    for st in block:
        stmtreads(st, out)
    return set(out)

def islocal(n):
    return n in localnames2

def alwaysexits(bl):
    if not bl:
        return False
    last = bl[-1]
    k = last[0]
    if k in ('return', 'break'):
        return True
    if k == 'do':
        return alwaysexits(last[1])
    if k == 'if' and last[2] is not None:
        return all((alwaysexits(b) for _, b in last[1])) and alwaysexits(last[2])
    return False

def namecount(stmts, x):
    n = 0

    def ev(e):
        nonlocal n
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        if e[0] == 'name' and e[1] == x:
            n += 1
        elif e[0] == 'index':
            ev(e[1])
            ev(e[2])
        elif e[0] == 'call':
            ev(e[1])
            for a in e[2]:
                ev(a)
        elif e[0] == 'method':
            ev(e[1])
            for a in e[3]:
                ev(a)
        elif e[0] == 'binop':
            ev(e[2])
            ev(e[3])
        elif e[0] == 'unop':
            ev(e[2])
        elif e[0] == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    ev(ke)
                ev(ve)

    def sv(st):
        nonlocal n
        k = st[0]
        if k == 'local':
            if x in st[1]:
                n += st[1].count(x)
            for e in st[2]:
                ev(e)
        elif k == 'assign':
            for t in st[1]:
                ev(t)
            for e in st[2]:
                ev(e)
        elif k == 'callstat':
            ev(st[1])
        elif k == 'return':
            for e in st[1]:
                ev(e)
        elif k == 'if':
            for c, b in st[1]:
                ev(c)
                for s2 in b:
                    sv(s2)
            if st[2] is not None:
                for s2 in st[2]:
                    sv(s2)
        elif k in ('while',):
            ev(st[1])
            for s2 in st[2]:
                sv(s2)
        elif k == 'repeat':
            for s2 in st[1]:
                sv(s2)
            ev(st[2])
        elif k == 'fornum':
            if st[1] == x:
                n += 1
            ev(st[2])
            ev(st[3])
            if st[4] is not None:
                ev(st[4])
            for s2 in st[5]:
                sv(s2)
        elif k == 'forin':
            n += st[1].count(x)
            for e in st[2]:
                ev(e)
            for s2 in st[3]:
                sv(s2)
        elif k == 'do':
            for s2 in st[1]:
                sv(s2)

    def evfuncs(e):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        if e[0] == 'func':
            if x in e[1]:
                n += e[1].count(x)
            for st in e[2]:
                svdeep(st)
        elif e[0] == 'index':
            evfuncs(e[1])
            evfuncs(e[2])
        elif e[0] == 'call':
            evfuncs(e[1])
            for a in e[2]:
                evfuncs(a)
        elif e[0] == 'method':
            evfuncs(e[1])
            for a in e[3]:
                evfuncs(a)
        elif e[0] in ('binop',):
            evfuncs(e[2])
            evfuncs(e[3])
        elif e[0] == 'unop':
            evfuncs(e[2])
        elif e[0] == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    evfuncs(ke)
                evfuncs(ve)

    def svdeep(st):
        sv(st)
        for e in exprsof(st):
            evfuncs(e)
    for st in stmts:
        svdeep(st)
    return n

def xvaluedeadfrom(stmts, j0, x):
    for j in range(j0, len(stmts)):
        st = stmts[j]
        c = namecount([st], x)
        if c == 0:
            continue
        if c == 1 and x in stmtwrites(st):
            return True
        return False
    return True

def closurementions(stmts, x):
    n = 0

    def evx(e):
        nonlocal n
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        k = e[0]
        if k == 'func':
            n += e[1].count(x) + namecount(e[2], x)
            return
        if k == 'index':
            evx(e[1])
            evx(e[2])
        elif k == 'call':
            evx(e[1])
            for a in e[2]:
                evx(a)
        elif k == 'method':
            evx(e[1])
            for a in e[3]:
                evx(a)
        elif k == 'binop':
            evx(e[2])
            evx(e[3])
        elif k == 'unop':
            evx(e[2])
        elif k == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    evx(ke)
                evx(ve)

    def svx(st):
        for e in exprsof(st):
            evx(e)
        for bl in subblocks(st):
            for s2 in bl:
                svx(s2)
    for st in stmts:
        svx(st)
    return n

def inlinetempsall(block):
    ch = [False]

    def run(stmts):
        i = 0
        while i < len(stmts):
            st = stmts[i]
            for bl in subblocks(st):
                run(bl)
            for f in stmtfuncs(st):
                run(f[2])
            x = rhs = None
            if st[0] == 'assign' and len(st[1]) == 1 and (st[1][0][0] == 'name') and (len(st[2]) == 1):
                x, rhs = (st[1][0][1], st[2][0])
            elif st[0] == 'local' and len(st[1]) == 1 and (len(st[2]) == 1):
                x, rhs = (st[1][0], st[2][0])
            if x is not None and i + 1 < len(stmts) and islocal(x):
                nxt = stmts[i + 1]
                if ismovable(rhs) and (not (rhs[0] == 'name' and rhs[1] == x)) and (closurementions(stmts[:i], x) == 0):
                    nx = None
                    if nxt[0] == 'assign' and len(nxt[1]) == 1 and (len(nxt[2]) == 1):
                        nx = nxt[2][0]
                    elif nxt[0] == 'local' and len(nxt[1]) == 1 and (len(nxt[2]) == 1):
                        nx = nxt[2][0]
                    if nx is not None and nx[0] == 'call' and (nx[1] == ['name', x]) and (not any((a == ['name', x] for a in nx[2]))):
                        nx[1] = cp(rhs)
                        del stmts[i]
                        ch[0] = True
                        continue
                if namecount([nxt], x) == 1 and xvaluedeadfrom(stmts, i + 2, x) and (closurementions(stmts[:i], x) == 0):

                    def usesafe(e):
                        if e == ['name', x]:
                            return True
                        if not isinstance(e, list) or not e:
                            return False
                        k = e[0]
                        if k == 'call':
                            return e[1] == ['name', x] or usesafe(e[1])
                        if k == 'method':
                            return e[1] == ['name', x]
                        if k == 'index':
                            return usesafe(e[1])
                        if k == 'binop':
                            return usesafe(e[2])
                        return False

                    def targetok(t):
                        if t[0] == 'name':
                            return True
                        return t[0] == 'index' and t[1][0] == 'name' and islocal(t[1][1])
                    ok = False
                    if ismovable(rhs) and (not (rhs[0] == 'name' and rhs[1] == x)):
                        if nxt[0] == 'local' and len(nxt[1]) == 1 and (len(nxt[2]) == 1):
                            ok = usesafe(nxt[2][0])
                        elif nxt[0] == 'assign' and len(nxt[1]) == 1 and (len(nxt[2]) == 1) and targetok(nxt[1][0]):
                            ok = usesafe(nxt[2][0])
                        elif nxt[0] == 'callstat':
                            ok = usesafe(nxt[1])
                    elif rhs[0] in ('call', 'method'):

                        def baseok(e):
                            if e == ['name', x]:
                                return True
                            if not isinstance(e, list) or not e:
                                return False
                            k = e[0]
                            if k == 'call':
                                return e[1] == ['name', x]
                            if k == 'method':
                                return e[1] == ['name', x]
                            if k == 'index':
                                return baseok(e[1])
                            return False
                        if nxt[0] == 'local' and len(nxt[1]) == 1 and (len(nxt[2]) == 1) and baseok(nxt[2][0]):
                            ok = True
                        elif nxt[0] == 'assign' and len(nxt[1]) == 1:
                            if len(nxt[2]) == 1 and baseok(nxt[2][0]) and targetok(nxt[1][0]):
                                ok = True
                            elif nxt[1][0][0] == 'index' and baseok(nxt[1][0][1]) and (len(nxt[2]) == 1):
                                ok = True
                        elif nxt[0] == 'callstat' and baseok(nxt[1]):
                            ok = True
                    if ok:
                        done = [False]
                        substnames(nxt, x, rhs, done)
                        if done[0]:
                            del stmts[i]
                            ch[0] = True
                            continue
            i += 1
    run(block)
    return ch[0]

def substnames(st, x, rhs, done):

    def ev(e):
        if done[0]:
            return e
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return e
        if e == ['name', x]:
            done[0] = True
            return cp(rhs)
        k = e[0]
        if k == 'index':
            e[1] = ev(e[1])
            e[2] = ev(e[2])
        elif k == 'call':
            e[1] = ev(e[1])
            e[2] = [ev(a) for a in e[2]]
        elif k == 'method':
            e[1] = ev(e[1])
            e[3] = [ev(a) for a in e[3]]
        elif k == 'binop':
            e[2] = ev(e[2])
            e[3] = ev(e[3])
        elif k == 'unop':
            e[2] = ev(e[2])
        elif k == 'table':
            e[1] = [[ev(ke) if ke is not None else None, ev(ve)] for ke, ve in e[1]]
        return e
    k = st[0]
    if k == 'local':
        st[2] = [ev(e) for e in st[2]]
    elif k == 'assign':
        for t in st[1]:
            if t[0] == 'index':
                t[1] = ev(t[1])
                t[2] = ev(t[2])
        st[2] = [ev(e) for e in st[2]]
    elif k == 'callstat':
        st[1] = ev(st[1])
    elif k == 'return':
        st[1] = [ev(e) for e in st[1]]
    elif k == 'if':
        for br in st[1]:
            br[0] = ev(br[0])
    elif k == 'while':
        st[1] = ev(st[1])
    elif k == 'repeat':
        st[2] = ev(st[2])
    elif k == 'fornum':
        st[2] = ev(st[2])
        st[3] = ev(st[3])
        if st[4] is not None:
            st[4] = ev(st[4])
    elif k == 'forin':
        st[2] = [ev(e) for e in st[2]]

def cleanupall(block):
    ch = [False]

    def clean(stmts):
        for st in stmts:
            for bl in subblocks(st):
                clean(bl)
            for f in stmtfuncs(st):
                clean(f[2])
        out = []
        for st in stmts:
            res = cleanstmt(st, ch)
            if res is not None:
                out.extend(res)
        for j, st in enumerate(out):
            if j < len(out) - 1 and (st[0] in ('return', 'break') or alwaysexits([st])):
                del out[j + 1:]
                ch[0] = True
                break
        stmts[:] = out
    clean(block)
    return ch[0]

def cleanstmt(st, ch):
    k = st[0]
    if k == 'local':
        if not st[1]:
            ch[0] = True
            return [] if not any((e[0] in ('call', 'method') for e in st[2])) else [['callstat', e] for e in st[2] if e[0] in ('call', 'method')]
        return [st]
    if k == 'assign':
        if len(st[1]) == 1 and st[1][0][0] == 'name' and (len(st[2]) == 1) and (st[2][0][0] == 'name') and (st[1][0][1] == st[2][0][1]) and ispure(st[2][0]):
            ch[0] = True
            return []
        return [st]
    if k == 'do':
        b = st[1]
        if not b:
            ch[0] = True
            return []
        if len(b) == 1 and b[0][0] == 'return':
            return [b[0]]
        if not blockhasflow(b):
            ch[0] = True
            return list(b)
        return [st]
    if k == 'if':
        return cleanif(st, ch)
    if k == 'while':
        return cleanwhile(st, ch)
    if k == 'repeat':
        if st[2] == ['true']:
            ch[0] = True
            return list(st[1])
        return [st]
    if k == 'fornum':
        if st[4] is not None and st[4] == ['num', '1']:
            st[4] = None
            ch[0] = True
        return [st]
    return [st]

def cleanif(st, ch):
    branches, els = (st[1], st[2])
    if els is not None and (not els):
        els = None
        ch[0] = True
    brs = []
    for c, b in branches:
        if not b and ispure(c):
            ch[0] = True
            continue
        brs.append([c, b])
    if not brs:
        if els is not None:
            ch[0] = True
            return list(els)
        ch[0] = True
        return []
    if len(brs) == 1:
        c, b = brs[0]
        if c == ['true']:
            ch[0] = True
            if els is not None:
                return list(b)
            if not b:
                return []
            return list(b)
        if c[0] in ('false', 'nil') and ispure(c):
            ch[0] = True
            if els is not None:
                return list(els)
            return []
        if not b and els is not None:
            nc = mapexpr(c, condrules(ch))
            nc = ['unop', 'not', nc]
            nc = mapexpr(nc, condrules(ch))
            ch[0] = True
            return [['if', [[nc, els]], None]]
        if not b and els is None:
            if c[0] in ('call', 'method'):
                ch[0] = True
                return [['callstat', c]]
    return [['if', brs, els]]

def cleanwhile(st, ch):
    cond, body = (st[1], st[2])
    if cond[0] in ('false', 'nil') and ispure(cond):
        ch[0] = True
        return []
    if cond == ['true'] and body:
        if body[0][0] == 'if':
            br = body[0]
            if len(br[1]) == 1 and br[2] is None and (br[1][0][1] == [['break']]):
                bc = br[1][0][0]
                nc = mapexpr(['unop', 'not', bc], condrules(ch))
                ch[0] = True
                return [['while', nc, body[1:]]]
        if body[-1][0] == 'if':
            br = body[-1]
            if len(br[1]) == 1 and br[2] is None and (br[1][0][1] == [['break']]):
                ch[0] = True
                return [['repeat', body[:-1], br[1][0][0]]]
    return [st]

def blockhasflow(block):
    for st in block:
        if st[0] in ('return', 'break'):
            return True
        for bl in subblocks(st):
            if blockhasflow(bl):
                return True
    return False

class interperror(Exception):
    pass

class breakex(Exception):
    pass

class returnex(Exception):

    def __init__(self, vals):
        self.vals = vals

class luatable:
    __slots__ = ('d', 'mt')

    def __init__(self):
        self.d = {}
        self.mt = None

    @staticmethod
    def norm(k):
        if isinstance(k, float) and k.is_integer() and (abs(k) <= 2 ** 53):
            return int(k)
        return k

    def rawget(self, k):
        return self.d.get(self.norm(k))

    def rawset(self, k, v):
        self.d[self.norm(k)] = v

    def length(self):
        n = 0
        while n + 1 in self.d:
            n += 1
            if n > 10 ** 7:
                raise interperror('table length runaway')
        return n

class closure:
    __slots__ = ('params', 'body', 'env')

    def __init__(self, params, body, env):
        self.params = params
        self.body = body
        self.env = env

class builtin:
    __slots__ = ('name', 'fn')

    def __init__(self, name, fn):
        self.name = name
        self.fn = fn

class env2:
    __slots__ = ('v', 'parent', 'varargs')

    def __init__(self, parent=None, varargs=None):
        self.v = {}
        self.parent = parent
        self.varargs = varargs if varargs is not None else []

    def lookup(self, n):
        e = self
        while e is not None:
            if n in e.v:
                return (True, e.v[n])
            e = e.parent
        return (False, None)

    def assign(self, n, val):
        e = self
        while e is not None:
            if n in e.v:
                e.v[n] = val
                return
            e = e.parent
        raise interperror('assignment to undeclared name %r' % n)

    def define(self, n, val):
        self.v[n] = val
miss = object()

class interp:
    maxsteps = 4000000
    maxdepth = 192

    def __init__(self):
        self.steps = self.maxsteps
        self.depth = 0
        self.globals = {}
        g = luatable()
        for nm, v in builtins.items():
            if callable(v) and (not isinstance(v, builtin)):
                v = builtin(nm, v)
            self.globals[nm] = v
            g.rawset(nm, v)
        g.rawset('_G', g)
        self.globals['_G'] = g

    @staticmethod
    def truthy(v):
        return v is not None and v is not False

    @staticmethod
    def tonum(v):
        if isinstance(v, bool):
            return None
        if isinstance(v, (int, float)):
            return float(v)
        if isinstance(v, str):
            try:
                return float(v.strip())
            except ValueError:
                return None
        return None

    def tostring(self, v):
        if v is None:
            return 'nil'
        if v is True:
            return 'true'
        if v is False:
            return 'false'
        if isinstance(v, (int, float)):
            return '%.14g' % float(v)
        if isinstance(v, str):
            return v
        if isinstance(v, luatable):
            return 'table: 0x0000'
        if isinstance(v, (closure, builtin)):
            return 'function: 0x0000'
        raise interperror('tostring %r' % (v,))

    def typ(self, v):
        if v is None:
            return 'nil'
        if isinstance(v, bool):
            return 'boolean'
        if isinstance(v, (int, float)):
            return 'number'
        if isinstance(v, str):
            return 'string'
        if isinstance(v, luatable):
            return 'table'
        if isinstance(v, (closure, builtin)):
            return 'function'
        raise interperror('type %r' % (v,))

    def eval(self, e, env):
        self.steps -= 1
        if self.steps <= 0:
            raise interperror('step budget exceeded')
        k = e[0]
        if k == 'num':
            return float(e[1])
        if k == 'str':
            return e[1]
        if k == 'nil':
            return None
        if k == 'true':
            return True
        if k == 'false':
            return False
        if k == 'name':
            found, v = env.lookup(e[1])
            if found:
                return v
            if e[1] in self.globals:
                return self.globals[e[1]]
            raise interperror('unknown global %r' % e[1])
        if k == 'index':
            return self.idxget(self.eval(e[1], env), self.eval(e[2], env))
        if k == 'call':
            vs = self.evalmulti(e, env)
            return vs[0] if vs else None
        if k == 'method':
            obj = self.eval(e[1], env)
            f = self.idxget(obj, e[2])
            return self.call(f, [obj] + self.evalargs(e[3], env))[0]
        if k == 'binop':
            op = e[1]
            if op == 'and':
                l = self.eval(e[2], env)
                return self.eval(e[3], env) if self.truthy(l) else l
            if op == 'or':
                l = self.eval(e[2], env)
                return l if self.truthy(l) else self.eval(e[3], env)
            l = self.eval(e[2], env)
            r = self.eval(e[3], env)
            if op == '..':
                return self.concat(l) + self.concat(r)
            if op in ('==', '~=', '<', '<=', '>', '>='):
                return self.compare(op, l, r)
            a, b = (self.tonum(l), self.tonum(r))
            if a is None or b is None:
                raise interperror('arith on non-number (%s)' % op)
            if op == '+':
                return a + b
            if op == '-':
                return a - b
            if op == '*':
                return a * b
            if op == '/':
                return a / b
            if op == '%':
                return a - lfloor(a / b) * b
            if op == '^':
                return a ** b
            raise interperror('bad binop %s' % op)
        if k == 'unop':
            op = e[1]
            if op == 'not':
                return not self.truthy(self.eval(e[2], env))
            if op == '-':
                n = self.tonum(self.eval(e[2], env))
                if n is None:
                    raise interperror('negate non-number')
                return -n
            if op == '#':
                v = self.eval(e[2], env)
                if isinstance(v, str):
                    return float(len(v))
                if isinstance(v, luatable):
                    return float(v.length())
                raise interperror('# on %s' % self.typ(v))
        if k == 'func':
            return closure(e[1], e[2], env)
        if k == 'table':
            t = luatable()
            n = 1
            for i, (ke, ve) in enumerate(e[1]):
                if ke is not None:
                    t.rawset(self.eval(ke, env), self.eval(ve, env))
                elif i == len(e[1]) - 1 and ve[0] in ('call', 'method', 'vararg'):
                    for v in self.evalmulti(ve, env):
                        t.rawset(float(n), v)
                        n += 1
                else:
                    t.rawset(float(n), self.eval(ve, env))
                    n += 1
            return t
        if k == 'vararg':
            return env.varargs[0] if env.varargs else None
        raise interperror('eval %r' % (e[:1],))

    def concat(self, v):
        if isinstance(v, str):
            return v
        if isinstance(v, bool):
            raise interperror('concat boolean')
        if isinstance(v, (int, float)):
            return '%.14g' % float(v)
        raise interperror('concat %s' % self.typ(v))

    def compare(self, op, l, r):
        if op == '==':
            return self.eq(l, r)
        if op == '~=':
            return not self.eq(l, r)
        ln, rn = (self.tonum(l), self.tonum(r))
        if ln is not None and rn is not None and (not isinstance(l, str)) and (not isinstance(r, str)):
            a, b = (ln, rn)
        elif isinstance(l, str) and isinstance(r, str):
            a, b = (l, r)
        else:
            raise interperror('compare %s %s' % (self.typ(l), self.typ(r)))
        if op == '<':
            return a < b
        if op == '<=':
            return a <= b
        if op == '>':
            return a > b
        if op == '>=':
            return a >= b
        raise interperror('bad compare')

    @staticmethod
    def eq(l, r):
        if isinstance(l, bool) or isinstance(r, bool):
            return l is r
        if isinstance(l, (int, float)) and isinstance(r, (int, float)):
            return float(l) == float(r)
        if type(l) is not type(r):
            return False
        if isinstance(l, (luatable, closure, builtin)):
            return l is r
        return l == r

    def idxget(self, obj, key):
        if isinstance(obj, luatable):
            k = luatable.norm(key)
            if k in obj.d:
                return obj.d[k]
            if obj.mt is not None:
                h = obj.mt.rawget('__index')
                if h is not None:
                    if isinstance(h, (closure, builtin)):
                        vs = self.call(h, [obj, key])
                        return vs[0] if vs else None
                    if isinstance(h, luatable):
                        return self.idxget(h, key)
            return None
        if isinstance(obj, str):
            st = self.globals.get('string')
            if isinstance(st, luatable):
                m = st.rawget(key)
                if m is not None:
                    return m
            return None
        if obj is None:
            raise interperror('index nil')
        raise interperror('index %s' % self.typ(obj))

    def idxset(self, obj, key, val):
        if not isinstance(obj, luatable):
            raise interperror('setindex %s' % self.typ(obj))
        obj.rawset(key, val)

    def evalargs(self, es, env):
        args = []
        for i, a in enumerate(es):
            if i == len(es) - 1 and a[0] in ('call', 'method', 'vararg'):
                args.extend(self.evalmulti(a, env))
            else:
                args.append(self.eval(a, env))
        return args

    def evalmulti(self, e, env):
        if e[0] == 'call':
            f = self.eval(e[1], env)
            return self.call(f, self.evalargs(e[2], env))
        if e[0] == 'method':
            obj = self.eval(e[1], env)
            f = self.idxget(obj, e[2])
            return self.call(f, [obj] + self.evalargs(e[3], env))
        if e[0] == 'vararg':
            return list(env.varargs)
        v = self.eval(e, env)
        return [v]

    def call(self, f, args):
        self.steps -= 1
        if self.steps <= 0:
            raise interperror('step budget exceeded')
        if isinstance(f, builtin):
            return f.fn(self, args)
        if isinstance(f, closure):
            if self.depth >= self.maxdepth:
                raise interperror('call depth')
            env = env2(f.env, varargs=[])
            for i, p in enumerate(f.params):
                if p == '...':
                    env.varargs = args[i:]
                    break
                env.define(p, args[i] if i < len(args) else None)
            self.depth += 1
            try:
                self.execblock(f.body, env)
            except returnex as r:
                return r.vals
            finally:
                self.depth -= 1
            return [None]
        raise interperror('call non-function %s' % (self.typ(f),))

    def execblock(self, stmts, env):
        for st in stmts:
            self.exec(st, env)

    def exec(self, st, env):
        self.steps -= 1
        if self.steps <= 0:
            raise interperror('step budget exceeded')
        k = st[0]
        if k == 'local':
            names, es = (st[1], st[2])
            vals = self.evallist(es, env, len(names)) if es else []
            for i, nm in enumerate(names):
                env.define(nm, vals[i] if i < len(vals) else None)
        elif k == 'assign':
            targets, es = (st[1], st[2])
            vals = self.evallist(es, env, len(targets))
            for i, t in enumerate(targets):
                v = vals[i] if i < len(vals) else None
                if t[0] == 'name':
                    env.assign(t[1], v)
                else:
                    self.idxset(self.eval(t[1], env), self.eval(t[2], env), v)
        elif k == 'if':
            for c, b in st[1]:
                if self.truthy(self.eval(c, env)):
                    self.execblock(b, env2(env))
                    return
            if st[2] is not None:
                self.execblock(st[2], env2(env))
        elif k == 'while':
            while self.truthy(self.eval(st[1], env)):
                try:
                    self.execblock(st[2], env2(env))
                except breakex:
                    break
        elif k == 'repeat':
            while True:
                try:
                    self.execblock(st[1], env2(env))
                except breakex:
                    break
                if self.truthy(self.eval(st[2], env)):
                    break
        elif k == 'fornum':
            var, e1, e2, e3, body = (st[1], st[2], st[3], st[4], st[5])
            a = self.tonum(self.eval(e1, env))
            b = self.tonum(self.eval(e2, env))
            c = self.tonum(self.eval(e3, env)) if e3 is not None else 1.0
            if a is None or b is None or c is None or (c == 0):
                raise interperror('bad fornum bounds')
            while c > 0 and a <= b or (c < 0 and a >= b):
                be = env2(env)
                be.define(var, a)
                try:
                    self.execblock(body, be)
                except breakex:
                    break
                a += c
        elif k == 'forin':
            names, es, body = (st[1], st[2], st[3])
            vals = self.evalmulti(es[-1], env) if es else []
            fs = [self.eval(x, env) for x in es[:-1]] + vals
            while len(fs) < 3:
                fs.append(None)
            f, s, ctl = (fs[0], fs[1], fs[2])
            while True:
                ret = self.call(f, [s, ctl])
                if not ret or ret[0] is None:
                    break
                ctl = ret[0]
                be = env2(env)
                for i, nm in enumerate(names):
                    be.define(nm, ret[i] if i < len(ret) else None)
                try:
                    self.execblock(body, be)
                except breakex:
                    break
        elif k == 'do':
            self.execblock(st[1], env2(env))
        elif k == 'return':
            raise returnex(self.evallist(st[1], env, -1) if st[1] else [])
        elif k == 'break':
            raise breakex()
        elif k == 'callstat':
            self.evalmulti(st[1], env)
        else:
            raise interperror('exec %r' % (k,))

    def evallist(self, es, env, want):
        out = []
        for i, e in enumerate(es):
            if i == len(es) - 1 and e[0] in ('call', 'method', 'vararg'):
                out.extend(self.evalmulti(e, env))
            else:
                out.append(self.eval(e, env))
        if want >= 0:
            if len(out) < want:
                out.extend([None] * (want - len(out)))
            elif len(out) > want:
                del out[want:]
        return out

def lfloor(x):
    import math
    return float(math.floor(x))

def lceil(x):
    import math
    return float(math.ceil(x))

def bichar(ip, args):
    out = []
    for a in args:
        n = ip.tonum(a)
        if n is None or not 0 <= n <= 255 or n != int(n):
            raise interperror('string.char(%r)' % (a,))
        out.append(chr(int(n)))
    return [''.join(out)]

def bibyte(ip, args):
    s = args[0] if args else None
    if not isinstance(s, str):
        raise interperror('string.byte non-string')
    i = int(ip.tonum(args[1])) if len(args) > 1 and ip.tonum(args[1]) is not None else 1
    j = int(ip.tonum(args[2])) if len(args) > 2 and ip.tonum(args[2]) is not None else i
    i = max(1, i if i > 0 else len(s) + i + 1)
    j = min(len(s), j if j > 0 else len(s) + j + 1)
    return [float(ord(s[k - 1])) for k in range(i, j + 1)]

def bisub(ip, args):
    s = args[0]
    if not isinstance(s, str):
        raise interperror('string.sub non-string')
    i = int(ip.tonum(args[1])) if len(args) > 1 and ip.tonum(args[1]) is not None else 1
    j = int(ip.tonum(args[2])) if len(args) > 2 and ip.tonum(args[2]) is not None else -1
    i = i if i > 0 else len(s) + i + 1
    j = j if j > 0 else len(s) + j + 1
    if i < 1:
        i = 1
    if j > len(s):
        j = len(s)
    return [s[i - 1:j] if i <= j else '']

def birep(ip, args):
    s = args[0]
    n = int(ip.tonum(args[1])) if len(args) > 1 else 0
    if not isinstance(s, str) or n < 0:
        raise interperror('string.rep')
    return [s * n]

def bislen(ip, args):
    s = args[0]
    if not isinstance(s, str):
        raise interperror('string.len')
    return [float(len(s))]

def bipack(ip, args):
    t = luatable()
    for i, a in enumerate(args):
        t.rawset(float(i + 1), a)
    t.rawset('n', float(len(args)))
    return [t]

def biunpack(ip, args):
    t = args[0] if args else None
    if not isinstance(t, luatable):
        raise interperror('table.unpack non-table')
    i = int(ip.tonum(args[1])) if len(args) > 1 and ip.tonum(args[1]) is not None else 1
    j = int(ip.tonum(args[2])) if len(args) > 2 and ip.tonum(args[2]) is not None else t.length()
    out = []
    for k in range(i, j + 1):
        out.append(t.rawget(float(k)))
    return out

def biinsert(ip, args):
    t = args[0]
    if not isinstance(t, luatable):
        raise interperror('table.insert')
    if len(args) >= 3:
        pos = int(ip.tonum(args[1]))
        n = t.length()
        for k in range(n, pos - 1, -1):
            t.rawset(float(k + 1), t.rawget(float(k)))
        t.rawset(float(pos), args[2])
    else:
        t.rawset(float(t.length() + 1), args[1])
    return []

def biconcat(ip, args):
    t = args[0]
    if not isinstance(t, luatable):
        raise interperror('table.concat')
    sep = args[1] if len(args) > 1 else ''
    i = int(ip.tonum(args[2])) if len(args) > 2 and ip.tonum(args[2]) is not None else 1
    j = int(ip.tonum(args[3])) if len(args) > 3 and ip.tonum(args[3]) is not None else t.length()
    parts = []
    for k in range(i, j + 1):
        v = t.rawget(float(k))
        parts.append(ip.concat(v) if not isinstance(v, str) else v)
    return [sep.join(parts)]

def bisetmetatable(ip, args):
    t = args[0]
    if not isinstance(t, luatable) or (len(args) > 1 and args[1] is not None and (not isinstance(args[1], luatable))):
        raise interperror('setmetatable')
    t.mt = args[1] if len(args) > 1 else None
    return [t]

def bigetmetatable(ip, args):
    t = args[0]
    return [t.mt if isinstance(t, luatable) else None]

def birawget(ip, args):
    t = args[0]
    if not isinstance(t, luatable):
        raise interperror('rawget')
    return [t.rawget(args[1])]

def birawset(ip, args):
    t = args[0]
    if not isinstance(t, luatable):
        raise interperror('rawset')
    t.rawset(args[1], args[2])
    return [t]

def birawequal(ip, args):
    return [ip.eq(args[0], args[1])]

def bitype(ip, args):
    return [ip.typ(args[0] if args else None)]

def bitostring(ip, args):
    return [ip.tostring(args[0] if args else None)]

def bitonumber(ip, args):
    if not args:
        return [None]
    v = ip.tonum(args[0])
    return [v]

def biselect(ip, args):
    if not args:
        raise interperror('select')
    if args[0] == '#':
        return [float(len(args) - 1)]
    n = int(ip.tonum(args[0]))
    if n < 0:
        n = len(args) + n
    return args[n:]

def bipcall(ip, args):
    if not args:
        raise interperror('pcall')
    try:
        return [True] + ip.call(args[0], args[1:])
    except interperror as e:
        return [False, 'interp: %s' % e]

def mktab(pairs):
    t = luatable()
    for k, v in pairs:
        t.rawset(k, builtin(k, v) if callable(v) else v)
    return t
builtins = {'string': mktab([('char', bichar), ('byte', bibyte), ('sub', bisub), ('rep', birep), ('len', bislen)]), 'table': mktab([('pack', bipack), ('unpack', biunpack), ('insert', biinsert), ('concat', biconcat)]), 'math': mktab([('floor', lambda ip, a: [lfloor(ip.tonum(a[0]))]), ('ceil', lambda ip, a: [lceil(ip.tonum(a[0]))]), ('abs', lambda ip, a: [abs(ip.tonum(a[0]))]), ('sqrt', lambda ip, a: [ip.tonum(a[0]) ** 0.5]), ('huge', float('inf')), ('pi', 3.141592653589793)]), 'setmetatable': bisetmetatable, 'getmetatable': bigetmetatable, 'rawget': birawget, 'rawset': birawset, 'rawequal': birawequal, 'type': bitype, 'tostring': bitostring, 'tonumber': bitonumber, 'select': biselect, 'pcall': bipcall}

def iterblocks(block):
    yield block
    for st in block:
        k = st[0]
        if k == 'if':
            for c, b in st[1]:
                for x in iterblocks(b):
                    yield x
            if st[2] is not None:
                for x in iterblocks(st[2]):
                    yield x
        elif k == 'while':
            for x in iterblocks(st[2]):
                yield x
        elif k == 'repeat':
            for x in iterblocks(st[1]):
                yield x
        elif k == 'fornum':
            for x in iterblocks(st[5]):
                yield x
        elif k == 'forin':
            for x in iterblocks(st[3]):
                yield x
        elif k == 'do':
            for x in iterblocks(st[1]):
                yield x
        for f in stmtfuncs(st):
            for x in iterblocks(f[2]):
                yield x

def exprsof(st):
    out = []

    def ev(e):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        k = e[0]
        out.append(e)
        if k == 'index':
            ev(e[1])
            ev(e[2])
        elif k == 'call':
            ev(e[1])
            for a in e[2]:
                ev(a)
        elif k == 'method':
            ev(e[1])
            for a in e[3]:
                ev(a)
        elif k == 'binop':
            ev(e[2])
            ev(e[3])
        elif k == 'unop':
            ev(e[2])
        elif k == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    ev(ke)
                ev(ve)
    for lst in stmtexprlists(st):
        for e in lst:
            ev(e)
    return out

def exprsdeep(st):
    out = exprsof(st)

    def more(bl):
        for s2 in bl:
            out.extend(exprsdeep(s2))
    for bl in subblocks(st):
        more(bl)
    for f in stmtfuncs(st):
        more(f[2])
    return out

def iterblocksnofuncs(block):
    yield block
    for st in block:
        k = st[0]
        if k == 'if':
            for c, b in st[1]:
                for x in iterblocksnofuncs(b):
                    yield x
            if st[2] is not None:
                for x in iterblocksnofuncs(st[2]):
                    yield x
        elif k == 'while':
            for x in iterblocksnofuncs(st[2]):
                yield x
        elif k == 'repeat':
            for x in iterblocksnofuncs(st[1]):
                yield x
        elif k == 'fornum':
            for x in iterblocksnofuncs(st[5]):
                yield x
        elif k == 'forin':
            for x in iterblocksnofuncs(st[3]):
                yield x
        elif k == 'do':
            for x in iterblocksnofuncs(st[1]):
                yield x

def lookslikefactory(funcnode):
    body = funcnode[2]
    strs = 0
    smtnames = set()
    smtcalled = [False]

    def visit(e):
        k = e[0]
        if k == 'str':
            if len(e[1]) >= 8:
                strscount[0] += 1
        elif k == 'index':
            if e[2] == ['str', 'setmetatable'] and e[1] == ['name', '_G']:
                pass
        elif k == 'call':
            c = e[1]
            if c[0] == 'name' and c[1] in smtnames:
                smtcalled[0] = True
    strscount = [0]
    for bl in iterblocksnofuncs(body):
        for st in bl:
            if st[0] == 'assign':
                for t, rhs in zip(st[1], st[2]):
                    if t[0] == 'name' and rhs == ['index', ['name', '_G'], ['str', 'setmetatable']]:
                        smtnames.add(t[1])
            for lst in stmtexprlists(st):
                stack = list(lst)
                while stack:
                    e = stack.pop()
                    if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
                        continue
                    k = e[0]
                    if k == 'str':
                        if len(e[1]) >= 8:
                            strscount[0] += 1
                    elif k == 'index':
                        stack.append(e[1])
                        stack.append(e[2])
                    elif k == 'call':
                        if e[1][0] == 'name' and e[1][1] in smtnames:
                            smtcalled[0] = True
                        stack.append(e[1])
                        stack.extend(e[2])
                    elif k == 'method':
                        stack.append(e[1])
                        stack.extend(e[3])
                    elif k == 'binop':
                        stack.append(e[2])
                        stack.append(e[3])
                    elif k == 'unop':
                        stack.append(e[2])
                    elif k == 'table':
                        for ke, ve in e[1]:
                            if ke is not None:
                                stack.append(ke)
                            stack.append(ve)
    return smtcalled[0] and strscount[0] >= 2

def numkey(e):
    if e[0] != 'num':
        return None
    try:
        return float(e[1])
    except ValueError:
        return None

def usesokafter(root, S, prodstmt):
    keys = []
    started = [False]

    def scanexpr(e):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return True
        k = e[0]
        if k == 'name':
            return e[1] != S
        if k == 'index':
            if e[1] == ['name', S]:
                nk = numkey(e[2])
                if nk is None:
                    return False
                keys.append(nk)
                return True
            return scanexpr(e[1]) and scanexpr(e[2])
        if k == 'call':
            return scanexpr(e[1]) and all((scanexpr(a) for a in e[2]))
        if k == 'method':
            return scanexpr(e[1]) and all((scanexpr(a) for a in e[3]))
        if k == 'binop':
            return scanexpr(e[2]) and scanexpr(e[3])
        if k == 'unop':
            return scanexpr(e[2])
        if k == 'table':
            for ke, ve in e[1]:
                if ke is not None and (not scanexpr(ke)):
                    return False
                if not scanexpr(ve):
                    return False
            return True
        return True

    def scanstmt(st):
        k = st[0]
        if k == 'assign':
            for t in st[1]:
                if t[0] == 'name' and t[1] == S:
                    return False
                if t[0] == 'index':
                    if t[1] == ['name', S]:
                        return False
                    if not (scanexpr(t[1]) and scanexpr(t[2])):
                        return False
        elif k == 'local':
            if S in st[1]:
                return False
        for lst in stmtexprlists(st):
            for e in lst:
                if not scanexpr(e):
                    return False
        return True

    def preok(e):
        k = e[0]
        if k == 'name' or k == 'func':
            return True
        if k == 'index':
            if e[1] == ['name', S]:
                return False
            return preok(e[1]) and preok(e[2])
        if k == 'call':
            return preok(e[1]) and all((preok(a) for a in e[2]))
        if k == 'method':
            return preok(e[1]) and all((preok(a) for a in e[3]))
        if k == 'binop':
            return preok(e[2]) and preok(e[3])
        if k == 'unop':
            return preok(e[2])
        if k == 'table':
            for ke, ve in e[1]:
                if ke is not None and (not preok(ke)):
                    return False
                if not preok(ve):
                    return False
            return True
        return True

    def full(bl):
        for st in bl:
            if st is prodstmt:
                started[0] = True
                continue
            if started[0]:
                if not scanstmt(st):
                    return False
            else:
                for lst in stmtexprlists(st):
                    for e in lst:
                        if not preok(e):
                            return False
            for bl2 in subblocks(st):
                if not full(bl2):
                    return False
            for f in stmtfuncs(st):
                if not full(f[2]):
                    return False
        return True
    if not full(root):
        return None
    return keys

def inlinestrtable(ast, verbose=False):
    cands = []
    for bl in iterblocks(ast):
        for i, st in enumerate(bl):
            if st[0] == 'assign' and len(st[1]) == 1 and (len(st[2]) == 1) and (st[1][0][0] == 'name') and (st[2][0][0] == 'func'):
                if lookslikefactory(st[2][0]):
                    cands.append((bl, i, st[1][0][1], st[2][0]))
            elif st[0] == 'local' and len(st[1]) == 1 and (len(st[2]) == 1) and (st[2][0][0] == 'func'):
                if lookslikefactory(st[2][0]):
                    cands.append((bl, i, st[1][0], st[2][0]))
    for blk, idx, fname, funcnode in cands:
        prod = None
        for j in range(idx + 1, len(blk)):
            st2 = blk[j]
            if st2[0] == 'assign' and len(st2[1]) == 1 and (len(st2[2]) == 1) and (st2[1][0][0] == 'name') and (st2[2][0] == ['call', ['name', fname], []]):
                prod = (j, st2[1][0][1])
                break
            wrote = False
            if st2[0] == 'assign':
                wrote = any((t[0] == 'name' and t[1] == fname for t in st2[1]))
            elif st2[0] == 'local' and fname in st2[1]:
                wrote = True
            if wrote:
                break
        if prod is None:
            continue
        pj, S = prod
        keys = usesokafter(ast, S, blk[pj])
        if not keys:
            continue
        try:
            ip = interp()
            f = closure(funcnode[1], funcnode[2], env2())
            tbl = ip.call(f, [])[0]
            if not isinstance(tbl, luatable):
                continue
            vals = {}
            for k in keys:
                v = ip.idxget(tbl, k)
                if not isinstance(v, str):
                    raise interperror('key %r -> %r' % (k, v))
                vals[k] = v
        except interperror as e:
            if verbose:
                print('  string factory not evaluated: %s' % e)
            continue
        active = [False]

        def rewrite(bl):
            for st in bl:
                if st is blk[pj]:
                    active[0] = True
                if active[0]:
                    for e in exprsdeep(st):
                        if e[0] == 'index' and e[1] == ['name', S]:
                            nk = numkey(e[2])
                            if nk is not None and nk in vals:
                                e[0] = 'str'
                                e[1] = vals[nk]
                                del e[2:]
                for bl2 in subblocks(st):
                    rewrite(bl2)
                for fn in stmtfuncs(st):
                    rewrite(fn[2])
        rewrite(ast)
        del blk[pj]
        del blk[idx]
        if verbose:
            print('  inlined %d runtime strings, factory removed' % len(vals))
        return True
    return False

def dbeeval(e, nils):
    k = e[0]
    if k == 'nil':
        return None
    if k == 'true':
        return True
    if k == 'false':
        return False
    if k == 'name':
        return None if e[1] in nils else 'unknown'
    if k == 'unop' and e[1] == 'not':
        v = dbeeval(e[2], nils)
        if v == 'unknown':
            return 'unknown'
        return not v
    if k == 'binop' and e[1] in ('==', '~='):
        a = dbeeval(e[2], nils)
        b = dbeeval(e[3], nils)
        if a == 'unknown' or b == 'unknown':
            return 'unknown'
        return a == b if e[1] == '==' else a != b
    return 'unknown'

def allwrites(block):
    out = set()
    for bl in iterblocks(block):
        for st in bl:
            out |= stmtwrites(st)
    return out

def funcenclosingwrites(st):
    out = set()
    for f in stmtfuncs(st):
        out |= allwrites(f[2])
    return out

def deadbranchelimall(block):
    ch = [False]
    dberun(block, set(), ch)
    for bl in iterblocks(block):
        for st in bl:
            for f in stmtfuncs(st):
                dberun(f[2], set(), ch)
    return ch[0]

def dberun(stmts, nils, ch):
    cur = set(nils)
    i = 0
    while i < len(stmts):
        st = stmts[i]
        k = st[0]
        if k == 'local':
            names, es = (st[1], st[2])
            if not es:
                cur.update(names)
            else:
                for j, nm in enumerate(names):
                    if j < len(es) and es[j] == ['nil']:
                        cur.add(nm)
                    else:
                        cur.discard(nm)
            cur -= funcenclosingwrites(st)
        elif k == 'assign':
            for j, t in enumerate(st[1]):
                if t[0] == 'name':
                    if j < len(st[2]) and st[2][j] == ['nil']:
                        cur.add(t[1])
                    else:
                        cur.discard(t[1])
            cur -= funcenclosingwrites(st)
        elif k == 'if':
            taken = None
            unknown = False
            for bi, (c, b) in enumerate(st[1]):
                v = dbeeval(c, cur)
                if v is True:
                    taken = bi
                    break
                if v == 'unknown':
                    unknown = True
                    break
            if taken is not None:
                stmts[i:i + 1] = st[1][taken][1]
                ch[0] = True
                continue
            if not unknown:
                els = st[2]
                if els is None:
                    del stmts[i]
                    ch[0] = True
                    continue
                stmts[i:i + 1] = els
                ch[0] = True
                continue
            exits = []
            for c, b in st[1]:
                exits.append(dberun(b, set(cur), ch))
            exits.append(dberun(st[2], set(cur), ch) if st[2] is not None else set(cur))
            cur = set.intersection(*[set(x) for x in exits])
            cur -= funcenclosingwrites(st)
        elif k == 'while':
            v = dbeeval(st[1], cur)
            if v is False:
                del stmts[i]
                ch[0] = True
                continue
            body = st[2]
            bodyentry = set(cur) - allwrites(body) - set(collectlocals(body))
            dberun(body, bodyentry, ch)
            cur -= allwrites(body) | set(collectlocals(body))
            cur -= funcenclosingwrites(st)
        elif k == 'repeat':
            body = st[1]
            bodyentry = set(cur) - allwrites(body) - set(collectlocals(body))
            dberun(body, bodyentry, ch)
            cur -= allwrites(body) | set(collectlocals(body))
            cur -= funcenclosingwrites(st)
        elif k == 'fornum':
            body = st[5]
            bodyentry = set(cur) - allwrites(body) - set(collectlocals(body))
            dberun(body, bodyentry, ch)
            cur -= allwrites(body) | set(collectlocals(body)) | {st[1]}
            cur -= funcenclosingwrites(st)
        elif k == 'forin':
            body = st[3]
            bodyentry = set(cur) - allwrites(body) - set(collectlocals(body))
            dberun(body, bodyentry, ch)
            cur -= allwrites(body) | set(collectlocals(body)) | set(st[1])
            cur -= funcenclosingwrites(st)
        elif k == 'do':
            dberun(st[1], set(cur), ch)
            cur -= allwrites(st[1]) | set(collectlocals(st[1]))
            cur -= funcenclosingwrites(st)
        elif k == 'callstat':
            cur -= funcenclosingwrites(st)
        i += 1
    return cur
envprobeglobals = ('getgenv', 'gethui')

def stripenvprobesall(block):
    ch = [False]

    def isproberhs(e):
        if e[0] == 'index' and e[1] == ['name', '_G'] and (e[2][0] == 'str') and (e[2][1] in envprobeglobals):
            return True
        if e[0] == 'call' and len(e[2]) == 0:
            return isproberhs(e[1])
        return False

    def isprobestmt(s, X):
        if s[0] == 'assign' and len(s[1]) == 1 and (len(s[2]) == 1) and (s[1][0] == ['name', X]):
            return isproberhs(s[2][0])
        if s[0] == 'callstat':
            return isproberhs(s[1])
        return False

    def namesin(e, out):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        if e[0] == 'name':
            out.append(e[1])
        elif e[0] == 'index':
            namesin(e[1], out)
            namesin(e[2], out)
        elif e[0] == 'call':
            namesin(e[1], out)
            for a in e[2]:
                namesin(a, out)
        elif e[0] == 'method':
            namesin(e[1], out)
            for a in e[3]:
                namesin(a, out)
        elif e[0] == 'binop':
            namesin(e[2], out)
            namesin(e[3], out)
        elif e[0] == 'unop':
            namesin(e[2], out)
        elif e[0] == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    namesin(ke, out)
                namesin(ve, out)

    def xsafeafter(bl, i, X):
        for st in bl[i + 1:]:
            if st[0] == 'assign':
                if any((t[0] == 'name' and t[1] == X for t in st[1])):
                    return True
            if st[0] == 'local' and X in st[1]:
                return True
            for e in exprsof(st):
                if e[0] == 'name' and e[1] == X:
                    return False
                if e[0] in ('call', 'method', 'func'):
                    return False
            if st[0] in ('if', 'while', 'repeat', 'fornum', 'forin'):
                return False
        return False

    def tryblock(bl):
        for i, st in enumerate(bl):
            if st[0] == 'if' and len(st[1]) == 1 and (st[2] is None):
                cond, body = st[1][0]
                nm = []
                namesin(cond, nm)
                xs = set(nm)
                if len(xs) == 1 and body:
                    X = next(iter(xs))
                    ok = all((isprobestmt(s, X) for s in body))
                    if ok and xsafeafter(bl, i, X):
                        del bl[i]
                        ch[0] = True
                        return True
            if st[0] in ('if', 'while', 'repeat', 'fornum', 'forin', 'do'):
                for bl2 in subblocks(st):
                    if tryblock(bl2):
                        return True
            for f in stmtfuncs(st):
                if tryblock(f[2]):
                    return True
        return False
    blroot = [block]
    while tryblock(block):
        pass
    return ch[0]

def ensuredecls(ast):
    locs, alln = collectallnames(ast)
    locs = set(locs)
    for bl in iterblocks(ast):
        for st in bl:
            for f in stmtfuncs(st):
                addparams(f, locs)
    missing = sorted((n for n in alln - locs if renpat.match(n)))
    if missing:
        ast.insert(0, ['local', missing, []])
    return missing
tempname = re.compile('^(?:v\\d+|[vaikc]p\\d+_\\d+|slp\\d+_\\d+|tp\\d+_\\d+|uvp\\d+_\\d+|pkp\\d+_\\d+|vap\\d+|rpp\\d+)$')

def scopefixdecls(funcnode):
    fixes = []

    def declarednames(f):
        out = set((p for p in f[1] if p != '...'))
        out.update(collectlocals(f[2]))
        return out

    def walkfunc(f, outerbound):
        boundhere = declarednames(f)
        env = outerbound | boundhere
        unbound = set()

        def exprwalk(e):
            if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
                return
            k = e[0]
            if k == 'name':
                if e[1] not in env and tempname.match(e[1]):
                    unbound.add(e[1])
            elif k == 'index':
                exprwalk(e[1])
                exprwalk(e[2])
            elif k == 'call':
                exprwalk(e[1])
                for a in e[2]:
                    exprwalk(a)
            elif k == 'method':
                exprwalk(e[1])
                for a in e[3]:
                    exprwalk(a)
            elif k == 'binop':
                exprwalk(e[2])
                exprwalk(e[3])
            elif k == 'unop':
                exprwalk(e[2])
            elif k == 'table':
                for ke, ve in e[1]:
                    if ke is not None:
                        exprwalk(ke)
                    exprwalk(ve)
            elif k == 'func':
                walkfunc(e, env)

        def walkstmts(stmts):
            for st in stmts:
                k = st[0]
                if k == 'local':
                    for e in st[2]:
                        exprwalk(e)
                elif k == 'assign':
                    for t in st[1]:
                        if t[0] == 'index':
                            exprwalk(t[1])
                            exprwalk(t[2])
                    for e in st[2]:
                        exprwalk(e)
                    for t in st[1]:
                        if t[0] == 'name' and t[1] not in env and tempname.match(t[1]):
                            unbound.add(t[1])
                elif k == 'callstat':
                    exprwalk(st[1])
                elif k == 'return':
                    for e in st[1]:
                        exprwalk(e)
                elif k == 'if':
                    for c, b in st[1]:
                        exprwalk(c)
                        walkstmts(b)
                    if st[2] is not None:
                        walkstmts(st[2])
                elif k == 'while':
                    exprwalk(st[1])
                    walkstmts(st[2])
                elif k == 'repeat':
                    walkstmts(st[1])
                    exprwalk(st[2])
                elif k == 'fornum':
                    for e in (st[2], st[3], st[4]):
                        if e is not None:
                            exprwalk(e)
                    walkstmts(st[5])
                elif k == 'forin':
                    for e in st[2]:
                        exprwalk(e)
                    walkstmts(st[3])
                elif k == 'do':
                    walkstmts(st[1])
        walkstmts(f[2])
        if unbound:
            f[2][:0] = [['local', sorted(unbound), []]]
            fixes.extend(((f, n) for n in sorted(unbound)))
    walkfunc(funcnode, set())
    return fixes

def addparams(funcnode, out):
    for p in funcnode[1]:
        out.add(p)
    for bl in iterblocks(funcnode[2]):
        for st in bl:
            for f in stmtfuncs(st):
                addparams(f, out)

def localizefirstuse(rootfunc):
    stats = [0, 0]

    def processfunc(f):
        body = f[2]
        closureat = {}

        def noteclosure(g, idx):
            m = []
            collectallmentions(g[2], m)
            m.extend((p for p in g[1] if p != '...'))
            for n in set(m):
                if n not in closureat or idx < closureat[n]:
                    closureat[n] = idx

        def scanclosures(stmts, idx):
            for st in stmts:
                for g in stmtfuncs(st):
                    noteclosure(g, idx)
                    scanclosures(g[2], idx)
                for bl in subblocks(st):
                    scanclosures(bl, idx)
        for i, st in enumerate(body):
            scanclosures([st], i)
        first = {}

        def note(n, ev):
            if n not in first:
                first[n] = ev

        def evreads(e):
            r = []
            exprreads(e, r)
            for n in r:
                note(n, 'read')

        def evstmt(st, tlidx):
            k = st[0]
            if k == 'local':
                for e in st[2]:
                    evreads(e)
                if not (tlidx is not None and (not st[2])):
                    for n in st[1]:
                        note(n, 'decl')
            elif k == 'assign':
                for t in st[1]:
                    if t[0] == 'index':
                        evreads(t[1])
                        evreads(t[2])
                for e in st[2]:
                    evreads(e)
                single = tlidx is not None and len(st[1]) == 1 and (len(st[2]) == 1)
                for t in st[1]:
                    if t[0] == 'name':
                        if single:
                            note(t[1], ('write', tlidx, True))
                        else:
                            note(t[1], 'write*')
            elif k == 'callstat':
                evreads(st[1])
            elif k == 'return':
                for e in st[1]:
                    evreads(e)
            elif k == 'if':
                for c, b in st[1]:
                    evreads(c)
                    for s2 in b:
                        evstmt(s2, None)
                if st[2] is not None:
                    for s2 in st[2]:
                        evstmt(s2, None)
            elif k == 'while':
                evreads(st[1])
                for s2 in st[2]:
                    evstmt(s2, None)
            elif k == 'repeat':
                for s2 in st[1]:
                    evstmt(s2, None)
                evreads(st[2])
            elif k == 'fornum':
                evreads(st[2])
                evreads(st[3])
                if st[4] is not None:
                    evreads(st[4])
                note(st[1], 'decl')
                for s2 in st[5]:
                    evstmt(s2, None)
            elif k == 'forin':
                for e in st[2]:
                    evreads(e)
                for n in st[1]:
                    note(n, 'decl')
                for s2 in st[3]:
                    evstmt(s2, None)
            elif k == 'do':
                for s2 in st[1]:
                    evstmt(s2, None)
        for i, st in enumerate(body):
            evstmt(st, i)
        edits = []
        for di, st in enumerate(body):
            if st[0] != 'local' or st[2]:
                continue
            keep, conv = ([], [])
            for n in st[1]:
                ev = first.get(n)
                if ev is None and n not in closureat:
                    continue
                ok = isinstance(ev, tuple) and ev[0] == 'write' and ev[2] and (ev[1] != di)
                if ok:
                    ca = closureat.get(n)
                    if ca is not None and ca <= ev[1]:
                        ok = False
                if ok:
                    conv.append(n)
                else:
                    keep.append(n)
            if conv:
                edits.append((di, keep, conv))
                stats[0] += len(conv)
                stats[1] += len(keep)
        for di, keep, conv in edits:
            for n in conv:
                ti = first[n][1]
                wst = body[ti]
                body[ti] = ['local', [n], wst[2]]
            if keep:
                body[di][1] = keep
            else:
                body[di] = None
        if any((st is None for st in body)):
            body[:] = [st for st in body if st is not None]

    def walk(f):
        processfunc(f)

        def walkstmts(stmts):
            for st in stmts:
                for g in stmtfuncs(st):
                    walk(g)
                for bl in subblocks(st):
                    walkstmts(bl)
        walkstmts(f[2])
    walk(rootfunc)
    return (stats[0], stats[1])

def collectallmentions(stmts, out):

    def ev(e):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        k = e[0]
        if k == 'name':
            out.append(e[1])
        elif k == 'index':
            ev(e[1])
            ev(e[2])
        elif k == 'call':
            ev(e[1])
            for a in e[2]:
                ev(a)
        elif k == 'method':
            ev(e[1])
            for a in e[3]:
                ev(a)
        elif k == 'binop':
            ev(e[2])
            ev(e[3])
        elif k == 'unop':
            ev(e[2])
        elif k == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    ev(ke)
                ev(ve)
        elif k == 'func':
            out.extend((p for p in e[1] if p != '...'))
            collectallmentions(e[2], out)

    def sv(st):
        k = st[0]
        if k == 'local':
            out.extend(st[1])
            for e in st[2]:
                ev(e)
        elif k == 'assign':
            for t in st[1]:
                ev(t)
            for e in st[2]:
                ev(e)
        elif k == 'callstat':
            ev(st[1])
        elif k == 'return':
            for e in st[1]:
                ev(e)
        elif k == 'if':
            for c, b in st[1]:
                ev(c)
                for s2 in b:
                    sv(s2)
            if st[2] is not None:
                for s2 in st[2]:
                    sv(s2)
        elif k == 'while':
            ev(st[1])
            for s2 in st[2]:
                sv(s2)
        elif k == 'repeat':
            for s2 in st[1]:
                sv(s2)
            ev(st[2])
        elif k == 'fornum':
            out.append(st[1])
            ev(st[2])
            ev(st[3])
            if st[4] is not None:
                ev(st[4])
            for s2 in st[5]:
                sv(s2)
        elif k == 'forin':
            out.extend(st[1])
            for e in st[2]:
                ev(e)
            for s2 in st[3]:
                sv(s2)
        elif k == 'do':
            for s2 in st[1]:
                sv(s2)
    for st in stmts:
        sv(st)
luakeywords = {'and', 'or', 'function', 'end', 'if', 'then', 'else', 'elseif', 'while', 'do', 'repeat', 'until', 'for', 'in', 'local', 'return', 'break', 'nil', 'true', 'false', 'not'}
ident = re.compile('^[A-Za-z_]\\w*$')
headerlocals = {'select', 'type', 'unpack', 'pairs', 'next', 'tostring', 'tonumber', 'table', 'math', 'string', '_G', 'main'}

def ungloball(funcnode):
    ch = [False]

    def rewrite(e, bound):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return e
        k = e[0]
        if k == 'index':
            e[1] = rewrite(e[1], bound)
            e[2] = rewrite(e[2], bound)
            if e[1] == ['name', '_G'] and e[2][0] == 'str' and ident.match(e[2][1]) and (e[2][1] not in luakeywords) and (e[2][1] not in bound):
                ch[0] = True
                return ['name', e[2][1]]
            return e
        if k == 'call':
            e[1] = rewrite(e[1], bound)
            e[2] = [rewrite(a, bound) for a in e[2]]
            return e
        if k == 'method':
            e[1] = rewrite(e[1], bound)
            e[3] = [rewrite(a, bound) for a in e[3]]
            return e
        if k == 'binop':
            e[2] = rewrite(e[2], bound)
            e[3] = rewrite(e[3], bound)
            return e
        if k == 'unop':
            e[2] = rewrite(e[2], bound)
            return e
        if k == 'table':
            e[1] = [[rewrite(ke, bound) if ke is not None else None, rewrite(ve, bound)] for ke, ve in e[1]]
            return e
        if k == 'func':
            inner = bound | set((p for p in e[1] if p != '...'))
            inner |= set(collectlocals(e[2]))
            walk(e[2], inner)
            return e
        return e

    def walk(stmts, bound):
        for st in stmts:
            k = st[0]
            if k == 'local':
                st[2] = [rewrite(e, bound) for e in st[2]]
                bound = bound | set(st[1])
            elif k == 'assign':
                for t in st[1]:
                    if t[0] == 'index':
                        t[1] = rewrite(t[1], bound)
                        t[2] = rewrite(t[2], bound)
                        if t[1] == ['name', '_G'] and t[2][0] == 'str' and ident.match(t[2][1]) and (t[2][1] not in luakeywords) and (t[2][1] not in bound) and (t[2][1] not in headerlocals):
                            t[0] = 'name'
                            t[1] = t[2][1]
                            del t[2]
                            ch[0] = True
                st[2] = [rewrite(e, bound) for e in st[2]]
            elif k == 'callstat':
                st[1] = rewrite(st[1], bound)
            elif k == 'return':
                st[1] = [rewrite(e, bound) for e in st[1]]
            elif k == 'if':
                for br in st[1]:
                    br[0] = rewrite(br[0], bound)
                    walk(br[1], bound)
                if st[2] is not None:
                    walk(st[2], bound)
            elif k == 'while':
                st[1] = rewrite(st[1], bound)
                walk(st[2], bound)
            elif k == 'repeat':
                walk(st[1], bound)
                st[2] = rewrite(st[2], bound)
            elif k == 'fornum':
                st[2] = rewrite(st[2], bound)
                st[3] = rewrite(st[3], bound)
                if st[4] is not None:
                    st[4] = rewrite(st[4], bound)
                walk(st[5], bound | {st[1]})
            elif k == 'forin':
                st[2] = [rewrite(e, bound) for e in st[2]]
                walk(st[3], bound | set(st[1]))
            elif k == 'do':
                walk(st[1], bound)
        return bound
    walk(funcnode[2], set())
    return ch[0]

def collectevents(body):
    evs = []
    ctr = [0]

    def add(tl, kind, name, depth):
        evs.append((ctr[0], tl, kind, name, depth))
        ctr[0] += 1

    def rd(e, tl, depth):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        k = e[0]
        if k == 'name':
            add(tl, 'r', e[1], depth)
        elif k == 'index':
            rd(e[1], tl, depth)
            rd(e[2], tl, depth)
        elif k == 'call':
            rd(e[1], tl, depth)
            for a in e[2]:
                rd(a, tl, depth)
        elif k == 'method':
            rd(e[1], tl, depth)
            for a in e[3]:
                rd(a, tl, depth)
        elif k == 'binop':
            rd(e[2], tl, depth)
            rd(e[3], tl, depth)
        elif k == 'unop':
            rd(e[2], tl, depth)
        elif k == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    rd(ke, tl, depth)
                rd(ve, tl, depth)

    def sv(st, tl, depth=0):
        k = st[0]
        if k == 'local':
            for e in st[2]:
                rd(e, tl, depth)
            for n in st[1]:
                add(tl, 'd', n, depth)
        elif k == 'assign':
            for t in st[1]:
                if t[0] == 'index':
                    rd(t[1], tl, depth)
                    rd(t[2], tl, depth)
            for e in st[2]:
                rd(e, tl, depth)
            for t in st[1]:
                if t[0] == 'name':
                    add(tl, 'w', t[1], depth)
        elif k == 'callstat':
            rd(st[1], tl, depth)
        elif k == 'return':
            for e in st[1]:
                rd(e, tl, depth)
        elif k == 'if':
            for c, b in st[1]:
                rd(c, tl, depth + 1)
                for s2 in b:
                    sv(s2, tl, depth + 1)
            if st[2] is not None:
                for s2 in st[2]:
                    sv(s2, tl, depth + 1)
        elif k == 'while':
            rd(st[1], tl, depth + 1)
            for s2 in st[2]:
                sv(s2, tl, depth + 1)
        elif k == 'repeat':
            for s2 in st[1]:
                sv(s2, tl, depth + 1)
            rd(st[2], tl, depth + 1)
        elif k == 'fornum':
            rd(st[2], tl, depth)
            rd(st[3], tl, depth)
            if st[4] is not None:
                rd(st[4], tl, depth)
            add(tl, 'd', st[1], depth)
            for s2 in st[5]:
                sv(s2, tl, depth + 1)
        elif k == 'forin':
            for e in st[2]:
                rd(e, tl, depth)
            for n in st[1]:
                add(tl, 'd', n, depth)
            for s2 in st[3]:
                sv(s2, tl, depth + 1)
        elif k == 'do':
            for s2 in st[1]:
                sv(s2, tl, depth)
    for tl, st in enumerate(body):
        sv(st, tl)
    return evs

def renamenonfunc(stmts, old, new):

    def ev(e):
        if not isinstance(e, list) or not e or (not isinstance(e[0], str)):
            return
        k = e[0]
        if k == 'name':
            if e[1] == old:
                e[1] = new
        elif k == 'index':
            ev(e[1])
            ev(e[2])
        elif k == 'call':
            ev(e[1])
            for a in e[2]:
                ev(a)
        elif k == 'method':
            ev(e[1])
            for a in e[3]:
                ev(a)
        elif k == 'binop':
            ev(e[2])
            ev(e[3])
        elif k == 'unop':
            ev(e[2])
        elif k == 'table':
            for ke, ve in e[1]:
                if ke is not None:
                    ev(ke)
                ev(ve)

    def sv(st):
        k = st[0]
        if k == 'local':
            for e in st[2]:
                ev(e)
        elif k == 'assign':
            for t in st[1]:
                if t[0] == 'index':
                    ev(t[1])
                    ev(t[2])
                elif t[0] == 'name' and t[1] == old:
                    t[1] = new
            for e in st[2]:
                ev(e)
        elif k == 'callstat':
            ev(st[1])
        elif k == 'return':
            for e in st[1]:
                ev(e)
        elif k == 'if':
            for br in st[1]:
                ev(br[0])
                for s2 in br[1]:
                    sv(s2)
            if st[2] is not None:
                for s2 in st[2]:
                    sv(s2)
        elif k == 'while':
            ev(st[1])
            for s2 in st[2]:
                sv(s2)
        elif k == 'repeat':
            for s2 in st[1]:
                sv(s2)
            ev(st[2])
        elif k == 'fornum':
            ev(st[2])
            ev(st[3])
            if st[4] is not None:
                ev(st[4])
            for s2 in st[5]:
                sv(s2)
        elif k == 'forin':
            for e in st[2]:
                ev(e)
            for s2 in st[3]:
                sv(s2)
        elif k == 'do':
            for s2 in st[1]:
                sv(s2)
    for st in stmts:
        sv(st)

def splitranges(rootfunc):
    stats = [0]
    mentions = [p for p in rootfunc[1] if p != '...']
    collectallmentions(rootfunc[2], mentions)
    mx = 0
    for n in mentions:
        m2 = re.match('^v(\\d+)$', n)
        if m2:
            mx = max(mx, int(m2.group(1)))
    fresh = [mx]

    def newname():
        fresh[0] += 1
        return 'v%d' % fresh[0]

    def process(f):
        body = f[2]
        changed = True
        while changed:
            changed = False
            localtemps = set((p for p in f[1] if p != '...')) | set(collectlocals(body))
            evs = collectevents(body)
            rng = {}
            for order, tl, k2, n2, d2 in evs:
                lo, hi = rng.get(tl, (order, order))
                rng[tl] = (min(lo, order), max(hi, order))
            for i, st in enumerate(body):
                if not (st[0] == 'assign' and len(st[1]) == 1 and (st[1][0][0] == 'name') and (len(st[2]) == 1)):
                    continue
                x = st[1][0][1]
                if x not in localtemps:
                    continue
                if st[2][0] == ['name', x]:
                    continue
                if closurementions(body, x):
                    continue
                ilo, ihi = rng.get(i, (10 ** 9, -1))
                if ilo > ihi:
                    continue
                spill = None
                for j in range(i):
                    s2 = body[j]
                    if s2[0] == 'assign' and len(s2[1]) == 1 and (s2[1][0][0] == 'name') and (len(s2[2]) == 1) and (s2[2][0] == ['name', x]):
                        y = s2[1][0][1]
                        if y != x and y in localtemps:
                            spill = (j, y)
                if spill is None:
                    continue
                j, y = spill
                jlo, jhi = rng.get(j, (10 ** 9, -1))
                ywmid = [e for e in evs if e[3] == y and e[2] == 'w' and (e[4] == 0) and (jhi < e[0] < ilo)]
                ydslater = [e for e in evs if e[3] == y and e[2] == 'd' and (e[0] > ihi)]
                yrsafter = [e for e in evs if e[3] == y and e[2] == 'r' and (e[0] > ihi)]
                xwbetween = [e for e in evs if e[3] == x and e[2] in ('w', 'd') and (jhi < e[0] < ilo)]
                xdslater = [e for e in evs if e[3] == x and e[2] == 'd' and (e[0] > ihi)]
                if not ywmid and (not ydslater) and yrsafter and (not xwbetween) and (not xdslater):
                    newn = newname()
                    renamenonfunc(body[i + 1:], x, newn)
                    body[i] = ['local', [newn], [st[2][0]]]
                    stats[0] += 1
                    changed = True
                    break
            if changed:
                continue
            for j, st in enumerate(body):
                if st[0] == 'assign' and len(st[1]) == 1 and (st[1][0][0] == 'name') and (len(st[2]) == 1) and (st[2][0][0] == 'name'):
                    y = st[1][0][1]
                    x = st[2][0][1]
                elif st[0] == 'local' and len(st[1]) == 1 and (len(st[2]) == 1) and (st[2][0][0] == 'name'):
                    y = st[1][0]
                    x = st[2][0][1]
                else:
                    continue
                if y == x or y not in localtemps or x not in localtemps:
                    continue
                if closurementions(body, y) or closurementions(body, x):
                    continue
                jlo, jhi = rng.get(j, (10 ** 9, -1))
                if jlo > jhi:
                    continue
                ywsafter = [e for e in evs if e[3] == y and e[2] == 'w' and (e[0] > jhi)]
                if any((e[4] == 0 for e in ywsafter)):
                    continue
                ydslater = [e for e in evs if e[3] == y and e[2] == 'd' and (e[0] > jhi)]
                xdslater = [e for e in evs if e[3] == x and e[2] == 'd' and (e[0] > jhi)]
                yrsafter = [e for e in evs if e[3] == y and e[2] == 'r' and (e[0] > jhi)]
                if ydslater or xdslater or (not yrsafter):
                    continue
                ylastread = max((e[0] for e in yrsafter))
                xwsafter = [e for e in evs if e[3] == x and e[2] == 'w' and (e[0] > jhi)]
                if any((e[0] <= ylastread for e in xwsafter)):
                    continue
                if ywsafter:
                    firstyw = min((e[0] for e in ywsafter))
                    if any((e[0] >= firstyw for e in evs if e[3] == x and e[2] == 'r' and (e[0] > jhi))):
                        continue
                renamenonfunc(body[j + 1:], y, x)
                del body[j]
                stats[0] += 1
                changed = True
                break

    def walk(f):
        process(f)

        def walkstmts(stmts):
            for st in stmts:
                for g in stmtfuncs(st):
                    walk(g)
                for bl in subblocks(st):
                    walkstmts(bl)
        walkstmts(f[2])
    walk(rootfunc)
    return stats[0]

def renameall(block):
    locs, alln = collectallnames(block)
    free = alln - locs
    avoid = free | keywords | {'main', 'select', 'type', 'unpack', 'pairs', 'next', 'tostring', 'tonumber', 'table', 'math', 'string', '_G', 'getfenv', 'setfenv', 'setmetatable', 'getmetatable', 'pcall', 'xpcall', 'error', 'assert', 'rawget', 'rawset', 'rawequal', 'print', 'load', 'loadstring', 'game', 'workspace', 'script', 'task', 'Instance', 'Enum', 'wait', 'typeof', 'tick', 'warn', 'delay', 'spawn'}

    def renamescope(stmts, params, visible):
        decls = [p for p in params if p != '...']
        for n in collectlocals(stmts):
            if n not in decls:
                decls.append(n)
        mapping = {}
        used = set(visible)
        ctr = 0
        for old in decls:
            if not renpat.match(old):
                continue
            while True:
                ctr += 1
                new = 'v%d' % ctr
                if new not in used:
                    break
            mapping[old] = new
            used.add(new)
        if mapping:
            applymapblock(stmts, mapping)
            params[:] = [mapping.get(p, p) for p in params]
        for f in iterfuncsblock(stmts):
            renamescope(f[2], f[1], used)
    renamescope(block, [], avoid)

def iterfuncsblock(stmts):
    out = []
    for st in stmts:
        collectfuncsstmt(st, out)
    return out

def collectfuncsstmt(st, out):
    for f in stmtfuncs(st):
        out.append(f)
    for bl in subblocks(st):
        for s2 in bl:
            collectfuncsstmt(s2, out)

def applymapblock(stmts, m):
    for st in stmts:
        k = st[0]
        if k == 'local':
            st[1] = [m.get(n, n) for n in st[1]]
            st[2] = [applymapexpr(e, m) for e in st[2]]
        elif k == 'assign':
            for t in st[1]:
                if t[0] == 'index':
                    t[1] = applymapexpr(t[1], m)
                    t[2] = applymapexpr(t[2], m)
                elif t[0] == 'name':
                    t[1] = m.get(t[1], t[1])
            st[2] = [applymapexpr(e, m) for e in st[2]]
        elif k == 'callstat':
            st[1] = applymapexpr(st[1], m)
        elif k == 'return':
            st[1] = [applymapexpr(e, m) for e in st[1]]
        elif k == 'if':
            for br in st[1]:
                br[0] = applymapexpr(br[0], m)
                applymapblock(br[1], m)
            if st[2] is not None:
                applymapblock(st[2], m)
        elif k == 'while':
            st[1] = applymapexpr(st[1], m)
            applymapblock(st[2], m)
        elif k == 'repeat':
            applymapblock(st[1], m)
            st[2] = applymapexpr(st[2], m)
        elif k == 'fornum':
            st[1] = m.get(st[1], st[1])
            st[2] = applymapexpr(st[2], m)
            st[3] = applymapexpr(st[3], m)
            if st[4] is not None:
                st[4] = applymapexpr(st[4], m)
            applymapblock(st[5], m)
        elif k == 'forin':
            st[1] = [m.get(n, n) for n in st[1]]
            st[2] = [applymapexpr(e, m) for e in st[2]]
            applymapblock(st[3], m)
        elif k == 'do':
            applymapblock(st[1], m)

def applymapexpr(e, m):
    k = e[0]
    if k == 'name':
        return ['name', m.get(e[1], e[1])]
    if k in ('num', 'str', 'nil', 'true', 'false', 'vararg'):
        return e
    if k == 'index':
        return ['index', applymapexpr(e[1], m), applymapexpr(e[2], m)]
    if k == 'call':
        return ['call', applymapexpr(e[1], m), [applymapexpr(a, m) for a in e[2]]]
    if k == 'method':
        return ['method', applymapexpr(e[1], m), e[2], [applymapexpr(a, m) for a in e[3]]]
    if k == 'binop':
        return ['binop', e[1], applymapexpr(e[2], m), applymapexpr(e[3], m)]
    if k == 'unop':
        return ['unop', e[1], applymapexpr(e[2], m)]
    if k == 'table':
        return ['table', [[applymapexpr(it[0], m) if it[0] is not None else None, applymapexpr(it[1], m)] for it in e[1]]]
    if k == 'func':
        body = list(e[2])
        applymapblock(body, m)
        return ['func', [m.get(p, p) for p in e[1]], body]
    raise polisherror('apply_map_expr: %s' % k)
prec = dict(binprec)
right = {'..', '^'}
maxp = 11

def isident(s):
    return bool(namere.match(s)) and s not in keywords

def quote(s):
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\t':
            out.append('\\t')
        elif ch == '\r':
            out.append('\\r')
        elif 32 <= o <= 126:
            out.append(ch)
        else:
            out.append('\\%03d' % o)
    out.append('"')
    return ''.join(out)

def prefixexp(e, pad):
    s = renderexpr(e, maxp, pad)
    if e[0] not in ('name', 'index', 'call', 'method'):
        return '(%s)' % s
    return s

def renderexpr(e, minp=0, pad=''):
    k = e[0]
    if k == 'name':
        s, p = (e[1], maxp)
    elif k == 'num':
        s, p = (e[1], maxp)
    elif k == 'str':
        s, p = (quote(e[1]), maxp)
    elif k in ('nil', 'true', 'false', 'vararg'):
        s = '...' if k == 'vararg' else k
        p = maxp
    elif k == 'binop':
        op = e[1]
        p = prec[op]
        if op in right:
            l = renderexpr(e[2], p + 1, pad)
            r = renderexpr(e[3], p, pad)
        else:
            l = renderexpr(e[2], p, pad)
            r = renderexpr(e[3], p + 1, pad)
        s = '%s %s %s' % (l, op, r)
    elif k == 'unop':
        op = e[1]
        p = unaryprec
        o = renderexpr(e[2], unaryprec, pad)
        if op == '-':
            if o.startswith('-'):
                o = '(%s)' % o
            s = '-' + o
        elif op == '#':
            s = '#' + o
        else:
            s = 'not ' + o
    elif k == 'index':
        p = maxp
        o = prefixexp(e[1], pad)
        key = e[2]
        if key[0] == 'str' and isident(key[1]):
            s = '%s.%s' % (o, key[1])
        else:
            s = '%s[%s]' % (o, renderexpr(key, 0, pad))
    elif k == 'call':
        p = maxp
        fs = prefixexp(e[1], pad)
        s = '%s(%s)' % (fs, ', '.join((renderexpr(a, 0, pad) for a in e[2])))
    elif k == 'method':
        p = maxp
        o = prefixexp(e[1], pad)
        s = '%s:%s(%s)' % (o, e[2], ', '.join((renderexpr(a, 0, pad) for a in e[3])))
    elif k == 'table':
        p = maxp
        parts = []
        for it in e[1]:
            if it[0] is None:
                parts.append(renderexpr(it[1], 0, pad))
            elif it[0][0] == 'str' and isident(it[0][1]):
                parts.append('%s = %s' % (it[0][1], renderexpr(it[1], 0, pad)))
            else:
                parts.append('[%s] = %s' % (renderexpr(it[0], 0, pad), renderexpr(it[1], 0, pad)))
        one = '{ %s }' % ', '.join(parts) if parts else '{}'
        if len(one) <= 78 and '\n' not in one:
            s = one
        else:
            inner = pad + '  '
            lines = []
            for it in e[1]:
                if it[0] is None:
                    lines.append(inner + renderexpr(it[1], 0, inner) + ',')
                elif it[0][0] == 'str' and isident(it[0][1]):
                    lines.append('%s%s = %s,' % (inner, it[0][1], renderexpr(it[1], 0, inner)))
                else:
                    lines.append('%s[%s] = %s,' % (inner, renderexpr(it[0], 0, inner), renderexpr(it[1], 0, inner)))
            s = '{\n' + '\n'.join(lines) + '\n' + pad + '}'
    elif k == 'func':
        p = maxp
        inner = pad + '  '
        lines = ['function(%s)' % ', '.join(e[1])]
        lines += renderblock(e[2], inner)
        lines.append(pad + 'end')
        s = '\n'.join(lines)
    else:
        raise polisherror('render_expr: %s' % k)
    if p < minp:
        return '(%s)' % s
    return s

def renderblock(stmts, ind):
    lines = []
    pad = ind if isinstance(ind, str) else '  ' * ind
    for st in stmts:
        lines += renderstmt(st, pad)
    return lines

def renderstmt(st, pad):
    k = st[0]
    if k == 'local':
        if st[2]:
            rhs = ', '.join((renderexpr(e, 0, pad) for e in st[2]))
            return [pad + 'local %s = %s' % (', '.join(st[1]), rhs)]
        lines = []
        first = True
        n = len(st[1])
        for i in range(0, n, 10):
            chunk = ', '.join(st[1][i:i + 10])
            if i + 10 < n:
                chunk += ','
            if first:
                lines.append(pad + 'local ' + chunk)
                first = False
            else:
                lines.append(pad + '       ' + chunk)
        return lines
    if k == 'assign':
        t = ', '.join((renderexpr(x, 0, pad) for x in st[1]))
        v = ', '.join((renderexpr(e, 0, pad) for e in st[2]))
        return [pad + '%s = %s' % (t, v)]
    if k == 'callstat':
        s = renderexpr(st[1], 0, pad)
        if s.startswith('('):
            s = ';' + s
        return [pad + s]
    if k == 'if':
        lines = []
        for bi, br in enumerate(st[1]):
            kw = 'if' if bi == 0 else 'elseif'
            lines.append(pad + '%s %s then' % (kw, renderexpr(br[0], 0, pad)))
            lines += renderblock(br[1], pad + '  ')
        if st[2] is not None:
            lines.append(pad + 'else')
            lines += renderblock(st[2], pad + '  ')
        lines.append(pad + 'end')
        return lines
    if k == 'while':
        return [pad + 'while %s do' % renderexpr(st[1], 0, pad)] + renderblock(st[2], pad + '  ') + [pad + 'end']
    if k == 'repeat':
        return [pad + 'repeat'] + renderblock(st[1], pad + '  ') + [pad + 'until %s' % renderexpr(st[2], 0, pad)]
    if k == 'fornum':
        head = '%s = %s, %s' % (st[1], renderexpr(st[2], 0, pad), renderexpr(st[3], 0, pad))
        if st[4] is not None:
            head += ', %s' % renderexpr(st[4], 0, pad)
        return [pad + 'for %s do' % head] + renderblock(st[5], pad + '  ') + [pad + 'end']
    if k == 'forin':
        return [pad + 'for %s in %s do' % (', '.join(st[1]), ', '.join((renderexpr(e, 0, pad) for e in st[2])))] + renderblock(st[3], pad + '  ') + [pad + 'end']
    if k == 'return':
        if not st[1]:
            return [pad + 'return']
        return [pad + 'return %s' % ', '.join((renderexpr(e, 0, pad) for e in st[1]))]
    if k == 'break':
        return [pad + 'break']
    if k == 'do':
        return [pad + 'do'] + renderblock(st[1], pad + '  ') + [pad + 'end']
    raise polisherror('render_stmt: %s' % k)

def render(block):
    return '\n'.join(renderblock(block, 0)) + '\n'

def countstmts(block):
    n = 0
    for st in block:
        n += 1
        for bl in subblocks(st):
            n += countstmts(bl)
        for f in stmtfuncs(st):
            n += countstmts(f[2])
    return n

def polish(src, verbose=False):
    marker = '\nlocal main = function('
    idx = src.find(marker)
    if idx < 0 or src.find(marker, idx + 1) != -1:
        raise polisherror('main-wrap marker not found')
    header = src[:idx + 1]
    body = src[idx + 1:]
    ast = parser(tokenize(body)).chunk()
    global localnames2, needsbind, allreads
    inlined = inlinestrtable(ast, verbose=verbose)
    locs, alln = collectallnames(ast)
    localnames2 = locs
    needsbind = computeneedsbinding(ast)
    allreads = allreadnames(ast)
    cw = closurewrittennames(ast)
    n0 = countstmts(ast)
    rounds = []
    for rnd in range(40):
        c1 = simplifyall(ast)
        c5 = deadbranchelimall(ast)
        c2 = copypropall(ast, cw, locs)
        c7 = inlinetempsall(ast)
        c3 = dceall(ast)
        c6 = stripenvprobesall(ast)
        c4 = cleanupall(ast)
        rounds.append((c1, c5, c2, c7, c3, c6, c4))
        if not (c1 or c5 or c2 or c7 or c3 or c6 or c4):
            break
    missing = ensuredecls(ast)
    if missing and verbose:
        print('  safety net: declared missing locals: %s' % ', '.join(missing))
    renameall(ast)
    nsplit = 0
    for outer in range(8):
        n = splitranges(ast[0][2][0])
        nsplit += n
        if not n:
            break
        locs, alln = collectallnames(ast)
        localnames2 = locs
        needsbind = computeneedsbinding(ast)
        allreads = allreadnames(ast)
        cw = closurewrittennames(ast)
        for rnd2 in range(10):
            c = simplifyall(ast) or deadbranchelimall(ast) or copypropall(ast, cw, locs) or inlinetempsall(ast) or dceall(ast) or stripenvprobesall(ast) or cleanupall(ast)
            if not c:
                break
    if verbose and nsplit:
        print('  split: %d register live ranges split' % nsplit)
    nconv, nkept = localizefirstuse(ast[0][2][0])
    if verbose and (nconv or nkept):
        print('  localize: %d locals declared at first use, %d kept at top' % (nconv, nkept))
    nung = ungloball(ast[0][2][0])
    if verbose and nung:
        print('  unglob: _G. prefixes dropped')
    scopefixes = scopefixdecls(ast[0][2][0])
    if scopefixes and verbose:
        print('  scope fix: declared %d missing locals across %d function(s)' % (len(scopefixes), len({id(f) for f, _ in scopefixes})))
    rendered = render(ast)
    ast2 = parser(tokenize(rendered)).chunk()
    n1 = countstmts(ast2)
    if not re.search('\\b_G\\b', rendered):
        nh = header.replace('local _G = getfenv and getfenv() or _G\n', '')
        if nh != header:
            header = nh
            if verbose:
                print('  env: unused _G binding line dropped from header')
    out = header + rendered
    if verbose:
        print('statements: %d -> %d%s' % (n0, n1, ' (string factory inlined)' if inlined else ''))
        for i, (c1, c5, c2, c7, c3, c6, c4) in enumerate(rounds):
            print('  round %d: simplify=%d deadbranch=%d copyprop=%d inline=%d dce=%d envprobe=%d cleanup=%d' % (i + 1, c1, c5, c2, c7, c3, c6, c4))
    return out

def main():
    args = sys.argv[1:]
    verbose = '--stats' in args
    args = [a for a in args if a != '--stats']
    if not args:
        print('usage: polish.py IN.lua [-o OUT.lua] [--stats]')
        return 1
    inp = args[0]
    outp = None
    if '-o' in args:
        outp = args[args.index('-o') + 1]
    src = open(inp, encoding='latin-1').read()
    res = polish(src, verbose=verbose)
    if outp:
        open(outp, 'w', encoding='latin-1').write(res)
        print('wrote %s (%d -> %d lines)' % (outp, src.count('\n'), res.count('\n')))
    else:
        sys.stdout.write(res)
    return 0
if __name__ == '__main__':
    sys.exit(main())
