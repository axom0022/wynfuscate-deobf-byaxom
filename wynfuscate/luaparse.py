from __future__ import annotations
import re

cf = re.compile('\\(\\d+(?:[*/+-]\\d+)+\\)')

def fold(text):
    prev = None
    while prev != text:
        prev = text
        text = re.sub('0x[0-9A-Fa-f]+', lambda m: str(int(m.group(0), 16)), text)
        text = cf.sub(lambda m: str(int(eval(m.group(0)))), text)
    return text
tokenre = re.compile('\n    (?P<num>0[xX][0-9a-fA-F]+|\\d+\\.\\d+(?:[eE][-+]?\\d+)?|\\d+)\n  | (?P<str>"(?:\\\\.|[^"\\\\])*"|\'(?:\\\\.|[^\'\\\\])*\')\n  | (?P<name>[A-Za-z_]\\w*)\n  | (?P<op>==|~=|<=|>=|\\.\\.\\.|\\.\\.|[-+*/%^#<>=(){}\\[\\];:,\\.])\n  | (?P<ws>\\s+)\n', re.X)
binops = {'or': 1, 'and': 2, '<': 3, '>': 3, '<=': 3, '>=': 3, '~=': 3, '==': 3, '..': 4, '+': 5, '-': 5, '*': 6, '/': 6, '%': 6, '^': 8}

def tokenize(s):
    toks, i = ([], 0)
    while i < len(s):
        m = tokenre.match(s, i)
        if not m:
            i += 1
            continue
        if m.lastgroup != 'ws':
            toks.append((m.lastgroup, m.group(0)))
        i = m.end()
    toks.append(('eof', ''))
    return toks

class parser:

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
            raise SyntaxError(f'expected {kind} {val!r} got {self.peek()}')
        return t

    def block(self, stop=('end',)):
        out = []
        while True:
            t = self.peek()
            if t[0] == 'eof':
                break
            if t[0] == 'name' and t[1] in stop:
                break
            if t[1] in ('else', 'elseif') and t[0] == 'name':
                break
            st = self.statement()
            if st is not None:
                out.append(st)
        return out

    def statement(self):
        t = self.peek()
        if t[0] == 'op' and t[1] == ';':
            self.next()
            return None
        if t[0] == 'name':
            w = t[1]
            if w == 'local':
                self.next()
                names = [self.expect('name')[1]]
                while self.accept('op', ','):
                    names.append(self.expect('name')[1])
                exprs = []
                if self.accept('op', '='):
                    exprs.append(self.expr())
                    while self.accept('op', ','):
                        exprs.append(self.expr())
                return ('local', names, exprs)
            if w == 'if':
                self.next()
                cond = self.expr()
                self.expect('name', 'then')
                then = self.block()
                elifs, els = ([], [])
                while True:
                    tt = self.peek()
                    if tt[0] == 'name' and tt[1] == 'elseif':
                        self.next()
                        c2 = self.expr()
                        self.expect('name', 'then')
                        elifs.append((c2, self.block()))
                    elif tt[0] == 'name' and tt[1] == 'else':
                        self.next()
                        els = self.block()
                        self.expect('name', 'end')
                        break
                    elif tt[0] == 'name' and tt[1] == 'end':
                        self.next()
                        break
                    else:
                        self.i += 1
                return ('if', cond, then, elifs, els)
            if w == 'while':
                self.next()
                cond = self.expr()
                self.expect('name', 'do')
                body = self.block()
                self.expect('name', 'end')
                return ('while', cond, body)
            if w == 'for':
                self.next()
                v1 = self.expect('name')[1]
                if self.accept('op', '='):
                    a = self.expr()
                    self.expect('op', ',')
                    b = self.expr()
                    c = None
                    if self.accept('op', ','):
                        c = self.expr()
                    self.expect('name', 'do')
                    body = self.block()
                    self.expect('name', 'end')
                    return ('fornum', v1, a, b, c, body)
                names = [v1]
                while self.accept('op', ','):
                    names.append(self.expect('name')[1])
                self.expect('name', 'in')
                it = self.expr()
                self.expect('name', 'do')
                body = self.block()
                self.expect('name', 'end')
                return ('forin', names, [it], body)
            if w == 'return':
                self.next()
                exprs = []
                nt = self.peek()
                if not (nt[0] == 'eof' or (nt[0] == 'name' and nt[1] == 'end')):
                    exprs.append(self.expr())
                    while self.accept('op', ','):
                        exprs.append(self.expr())
                return ('return', exprs)
            if w == 'do':
                self.next()
                b = self.block()
                self.expect('name', 'end')
                return ('do', b)
            if w == 'repeat':
                self.next()
                b = self.block(stop=('until',))
                self.expect('name', 'until')
                return ('repeat', b, self.expr())
            if w == 'break':
                self.next()
                return ('break',)
        e = self.suffixed()
        if self.accept('op', '='):
            return ('assign', e, self.expr())
        if self.peek()[1] == ',' and self.peek()[0] == 'op':
            targets = [e]
            while self.accept('op', ','):
                targets.append(self.suffixed())
            self.expect('op', '=')
            exprs = [self.expr()]
            while self.accept('op', ','):
                exprs.append(self.expr())
            return ('massign', targets, exprs)
        return ('callstat', e)

    def expr(self, minp=0):
        t = self.peek()
        left = None
        if t[0] == 'name' and t[1] in ('not',):
            self.next()
            left = ('un', 'not', self.expr(7))
        elif t[0] == 'op' and t[1] in ('-', '#'):
            self.next()
            left = ('un', t[1], self.expr(7))
        elif t[0] == 'op' and t[1] == '(':
            self.next()
            left = self.expr()
            self.expect('op', ')')
            left = self.suffixedfrom(left)
        elif t[0] == 'name' and t[1] == 'function':
            self.next()
            params = []
            if self.accept('op', '('):
                while not self.accept('op', ')'):
                    if self.peek()[1] == '...':
                        self.next()
                        params.append('...')
                    else:
                        params.append(self.expect('name')[1])
                    if not self.accept('op', ','):
                        self.expect('op', ')')
                        break
            body = self.block()
            self.expect('name', 'end')
            left = ('function', params, body)
        else:
            left = self.suffixed()
        while True:
            t = self.peek()
            if (t[0] == 'name' or t[0] == 'op') and t[1] in binops and (binops[t[1]] > minp):
                self.next()
                right = self.expr(binops[t[1]] - (1 if t[1] == '^' else 0))
                left = ('bin', t[1], left, right)
            else:
                break
        return left

    def suffixed(self):
        return self.suffixedfrom(self.primary())

    def suffixedfrom(self, e):
        while True:
            t = self.peek()
            if t[0] == 'op' and t[1] == '[':
                self.next()
                idx = self.expr()
                self.expect('op', ']')
                e = ('index', e, idx)
            elif t[0] == 'op' and t[1] == '.':
                self.next()
                e = ('index', e, ('lit', self.expect('name')[1]))
            elif t[0] == 'op' and t[1] == ':':
                self.next()
                nm = ('str', self.expect('name')[1])
                self.expect('op', '(')
                args = []
                while not self.accept('op', ')'):
                    args.append(self.expr())
                    if not self.accept('op', ','):
                        self.expect('op', ')')
                        break
                e = ('call', ('index', e, nm), [e] + args)
            elif t[0] == 'op' and t[1] == '(':
                self.next()
                args = []
                while not self.accept('op', ')'):
                    args.append(self.expr())
                    if not self.accept('op', ','):
                        self.expect('op', ')')
                        break
                e = ('call', e, args)
            else:
                break
        return e

    def primary(self):
        t = self.peek()
        if t[0] == 'num':
            self.next()
            v = t[1]
            if v[:2].lower() == '0x':
                return ('num', int(v, 16))
            if '.' in v or 'e' in v or 'E' in v:
                return ('num', float(v))
            return ('num', int(v))
        if t[0] == 'str':
            self.next()
            return ('str', t[1][1:-1])
        if t[0] == 'name':
            self.next()
            if t[1] == 'true':
                return ('bool', True)
            if t[1] == 'false':
                return ('bool', False)
            if t[1] == 'nil':
                return ('nilv',)
            return ('var', t[1])
        if t[0] == 'op' and t[1] == '...':
            self.next()
            return ('vararg',)
        if t[0] == 'op' and t[1] == '{':
            self.next()
            items = []
            while not self.accept('op', '}'):
                if self.peek()[0] == 'op' and self.peek()[1] == '[':
                    self.next()
                    k = self.expr()
                    self.expect('op', ']')
                    self.expect('op', '=')
                    items.append(('pair', k, self.expr()))
                elif self.peek()[0] == 'name' and self.peek()[1] not in ('not', 'nil', 'true', 'false', 'function'):
                    save = self.i
                    k = self.next()[1]
                    if self.accept('op', '='):
                        items.append(('pair', ('lit', k), self.expr()))
                    else:
                        self.i = save
                        items.append(('item', self.expr()))
                else:
                    items.append(('item', self.expr()))
                if not self.accept('op', ','):
                    if not self.accept('op', ';'):
                        self.expect('op', '}')
                        break
            return ('table', items)
        raise SyntaxError(f'unexpected {t}')

def parselua(body):
    try:
        return parser(tokenize(body)).block(stop=())
    except (SyntaxError, IndexError, RecursionError):
        return None
