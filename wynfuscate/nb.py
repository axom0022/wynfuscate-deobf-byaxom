from __future__ import annotations
import re
from .semant import L

decfix = re.compile('DEC\\(+\\s*\\(?(\\d+)\\)?\\s*,\\s*KEY\\s*\\)+')

def nbclean(nb):
    return decfix.sub('DEC(\\1,KEY)', nb)
nbtok = re.compile('\n    (?P<ws>\\s+)\n  | (?P<num>0[xX][0-9a-fA-F]+|\\d+\\.\\d+|\\d+)\n  | (?P<str>"(?:\\\\.|[^"\\\\])*"|\'(?:\\\\.|[^\'\\\\])*\')\n  | (?P<at>@[0-9]+)\n  | (?P<name>[A-Za-z_]\\w*)\n  | (?P<op>==|~=|<=|>=|\\.\\.\\.|\\.\\.|[-+*/%^#<>=(){}\\[\\];:,.])\n', re.X)

def nbtokens(s):
    toks, i = ([], 0)
    while i < len(s):
        m = nbtok.match(s, i)
        if not m:
            raise nberror('tokenize at %d: %r' % (i, s[i:i + 30]))
        i = m.end()
        if m.lastgroup == 'ws':
            continue
        if m.lastgroup == 'name':
            parts = splitgluedname(m.group(0))
            if parts:
                for p in parts:
                    toks.append(('name', p))
                continue
        toks.append((m.lastgroup, m.group(0)))
    toks.append(('eof', ''))
    return toks
luakeywords = {'end', 'then', 'do', 'else', 'elseif', 'if', 'while', 'for', 'local', 'return', 'break', 'and', 'or', 'not', 'nil', 'true', 'false', 'function', 'repeat', 'until', 'in'}
knownnames = set()

def registernames(names):
    knownnames.update(names)
namere = re.compile('[A-Za-z_]\\w*')

def collectnamesfromnbs(nbs):
    cnt = {}
    for nb in nbs:
        for m in namere.finditer(nb):
            n = m.group(0)
            cnt[n] = cnt.get(n, 0) + 1
    known = {n for n, c in cnt.items() if c >= 2 or len(n) <= 3}
    knownnames.update(known)
    knownnames.update(builtinnames)
    return known

def splitgluedname(tok):
    if tok in knownnames or tok in luakeywords:
        return None
    parts, i, n = ([], 0, len(tok))
    while i < n:
        best = None
        for L in range(min(n - i, 16), 0, -1):
            cand = tok[i:i + L]
            if cand in knownnames or cand in luakeywords:
                best = cand
                break
        if best is None:
            return None
        parts.append(best)
        i += len(best)
    return parts if len(parts) >= 2 else None

def unquote(lit):
    body = lit[1:-1]
    out, i = ([], 0)
    while i < len(body):
        c = body[i]
        if c == '\\' and i + 1 < len(body):
            n = body[i + 1]
            if n.isdigit():
                j = i + 1
                while j < len(body) and body[j].isdigit() and (j - i <= 3):
                    j += 1
                out.append(chr(int(body[i + 1:j]) % 256))
                i = j
                continue
            out.append({'n': '\n', 't': '\t', '\\': '\\', '"': '"', "'": "'"}.get(n, n))
            i += 2
            continue
        out.append(c)
        i += 1
    return ''.join(out)

class nberror(Exception):
    pass
binopprio = {'or': 1, 'and': 2, '<': 3, '>': 3, '<=': 3, '>=': 3, '~=': 3, '==': 3, '..': 4, '+': 5, '-': 5, '*': 6, '/': 6, '%': 6, '^': 8}
rightassoc = {'^'}

class nbparser:

    def __init__(self, toks):
        self.toks, self.i = (toks, 0)

    def peek(self, k=0):
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def accept(self, kind, val=None):
        t = self.peek()
        if t[0] == kind and (val is None or t[1] == val):
            return self.next()
        return None

    def expect(self, kind, val=None):
        t = self.accept(kind, val)
        if not t:
            raise nberror('expected %s %r got %s %r (ctx %s)' % (kind, val, self.peek()[0], self.peek()[1], ' '.join((x[1] for x in self.toks[max(0, self.i - 6):self.i + 6]))))
        return t

    def block(self, stop=('end', 'else', 'elseif')):
        out = []
        while True:
            t = self.peek()
            if t[0] == 'eof':
                break
            if t[0] == 'name' and t[1] in stop:
                break
            if t == ('op', ';'):
                self.next()
                continue
            st = self.statement()
            if st is not None:
                out.append(st)
        return out

    def statement(self):
        t = self.peek()
        if t[0] == 'name':
            if t[1] == 'local':
                return self.localstmt()
            if t[1] == 'if':
                return self.ifstmt()
            if t[1] == 'while':
                return self.whilestmt()
            if t[1] == 'for':
                return self.forstmt()
            if t[1] == 'do':
                self.next()
                b = self.block()
                self.expect('name', 'end')
                return ('do', b)
            if t[1] == 'return':
                self.next()
                nxt = self.peek()
                if nxt[0] == 'name' and nxt[1] in ('end', 'else', 'elseif') or nxt[0] == 'eof':
                    return ('return', None)
                return ('return', self.exprlist())
            if t[1] == 'break':
                self.next()
                return ('break',)
            if t[1] in ('then', 'end', 'else', 'elseif', 'and', 'or', 'not', 'nil', 'true', 'false', 'while', 'for', 'function'):
                raise nberror('unexpected keyword %r' % t[1])
        e = self.suffixed()
        if self.accept('op', '='):
            rhs = self.exprlist()
            if e[0] not in ('name', 'index', 'at'):
                raise nberror('bad assignment target %r' % (e,))
            return ('assign', [e], rhs)
        if self.accept('op', ','):
            tgts = [e]
            while True:
                tgts.append(self.suffixed())
                if not self.accept('op', ','):
                    break
            self.expect('op', '=')
            return ('assign', tgts, self.exprlist())
        if e[0] != 'call':
            raise nberror('expression statement is not a call: %r' % (e,))
        return ('callstat', e)

    def localstmt(self):
        self.expect('name', 'local')
        if self.peek() == ('name', 'function'):
            raise nberror('local function literals not supported')
        names = [self.expect('name')[1]]
        while self.accept('op', ','):
            names.append(self.expect('name')[1])
        exprs = []
        if self.accept('op', '='):
            exprs = self.exprlist()
        return ('local', names, exprs)

    def ifstmt(self):
        self.expect('name', 'if')
        branches = []
        cond = self.expr()
        self.expect('name', 'then')
        branches.append((cond, self.block()))
        els = None
        while True:
            if self.accept('name', 'elseif'):
                c = self.expr()
                self.expect('name', 'then')
                branches.append((c, self.block()))
                continue
            if self.accept('name', 'else'):
                els = self.block()
            self.expect('name', 'end')
            break
        return ('if', branches, els)

    def whilestmt(self):
        self.expect('name', 'while')
        c = self.expr()
        self.expect('name', 'do')
        b = self.block()
        self.expect('name', 'end')
        return ('while', c, b)

    def forstmt(self):
        self.expect('name', 'for')
        v1 = self.expect('name')[1]
        if self.accept('op', '='):
            a = self.expr()
            self.expect('op', ',')
            b = self.expr()
            c = self.expr() if self.accept('op', ',') else ('num', 1)
            self.expect('name', 'do')
            body = self.block()
            self.expect('name', 'end')
            return ('fornum', v1, a, b, c, body)
        vars = [v1]
        while self.accept('op', ','):
            vars.append(self.expect('name')[1])
        self.expect('name', 'in')
        e = self.expr()
        self.expect('name', 'do')
        body = self.block()
        self.expect('name', 'end')
        return ('forin', vars, e, body)

    def exprlist(self):
        out = [self.expr()]
        while self.accept('op', ','):
            out.append(self.expr())
        return out

    def expr(self, minp=0):
        left = self.unary()
        while True:
            t = self.peek()
            op = None
            if t[0] == 'op' and t[1] in binopprio:
                op = t[1]
            elif t[0] == 'name' and t[1] in ('and', 'or'):
                op = t[1]
            if op is None or binopprio[op] <= minp:
                return left
            self.next()
            p = binopprio[op]
            if op in rightassoc:
                p -= 1
            right = self.expr(p)
            if op == 'and':
                left = ('and', left, right)
            elif op == 'or':
                left = ('or', left, right)
            else:
                left = ('bin', op, left, right)

    def unary(self):
        t = self.peek()
        if t == ('op', '-'):
            self.next()
            return ('un', '-', self.unary())
        if t == ('op', '#'):
            self.next()
            return ('un', '#', self.unary())
        if t == ('name', 'not'):
            self.next()
            return ('un', 'not', self.unary())
        return self.suffixed()

    def suffixed(self):
        e = self.primary()
        while True:
            if self.accept('op', '.'):
                key = self.expect('name')[1]
                e = ('index', e, ('str', key))
                continue
            if self.peek() == ('op', '['):
                self.next()
                k = self.expr()
                self.expect('op', ']')
                e = ('index', e, k)
                continue
            if self.peek() == ('op', '('):
                self.next()
                args = []
                if self.peek() != ('op', ')'):
                    args = self.exprlist()
                self.expect('op', ')')
                e = ('call', e, args)
                continue
            return e

    def primary(self):
        t = self.next()
        if t[0] == 'num':
            v = t[1]
            if v.lower().startswith('0x'):
                return ('num', int(v, 16))
            if '.' in v:
                return ('num', float(v))
            return ('num', int(v))
        if t[0] == 'str':
            return ('str', unquote(t[1]))
        if t[0] == 'at':
            return ('at', int(t[1][1:]))
        if t[0] == 'name':
            if t[1] == 'true':
                return ('true',)
            if t[1] == 'false':
                return ('false',)
            if t[1] == 'nil':
                return ('nil',)
            if t[1] in ('function', 'end', 'then', 'do', 'and', 'or', 'not'):
                raise nberror('unexpected keyword in expr: %r' % t[1])
            return ('name', t[1])
        if t == ('op', '('):
            e = self.expr()
            self.expect('op', ')')
            return e
        if t == ('op', '{'):
            items = []
            if self.peek() != ('op', '}'):
                items = self.exprlist()
            self.expect('op', '}')
            return ('tabcon', items)
        raise nberror('primary got %s %r' % (t[0], t[1]))
nbparsecache = {}

def nbparse(nb):
    ast = nbparsecache.get(nb)
    if ast is None:
        p = nbparser(nbtokens(nb))
        ast = p.block()
        if p.peek()[0] != 'eof':
            raise nberror('trailing tokens: %r' % (p.peek(),))
        nbparsecache[nb] = ast
    return ast
builtinnames = {'R', 'Mp', 'TOP', 'MT', 'ENV', 'UPV', 'Mj', 'MAP', 'tZ', 'HS', 'POOL', 'KEY', 'DEC', 'UK', 'Ue', 'UF', 'UFX', 'UY', 'UR', 'PROTOS', 'MZ', 'Jq', 'Mi', 'Md', 'MY', 'n3', 'gA', 'q7', 'O0', 'zj', 'Iv', 'zU', 'Ia', 'zM', 'IM', 'zH', 'Ix', 'zx', 'Ik', 'zr', 'zt', 'Im', 'MI', 'QZ', 'MB', 'bO', 'MD', 'Q6', 'CELLS', 'MJ', 'Q9', 'Mx', 'Q7', 'MH', 'nV', 'Og', 'nE', 'OJ', 'zm', 'n8', 'O9', 'zk', 'IF', 'IZ', 'PC', 'XOR'}
