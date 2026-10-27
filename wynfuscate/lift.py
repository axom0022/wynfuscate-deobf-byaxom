from __future__ import annotations
import re
from .semant import loadlibtable
from .decode import decodeall, resolveconst
from .ir import S

def q2(s):
    if isinstance(s, str):
        return '"' + s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n').replace('\r', '\\r').replace('\x00', '\\0') + '"'
    if isinstance(s, float) and s == int(s) and (abs(s) < 1000000000000000.0):
        return str(int(s))
    return repr(s)

class protolifter:

    def __init__(self, sem, P, protos):
        self.sem = sem
        self.P = P
        self.protos = protos
        self.dec = decodeall(sem, P)
        self.byi = {d['i']: d for d in self.dec}
        self.n = P['n']

    def K(self, d, k=0):
        cv = d.get('consts', [])
        if k < len(cv):
            return resolveconst(self.sem, cv[k])
        return None

    def regs(self, d):
        return d['cols']

    def lift(self):
        lines = []
        labels = set()
        for d in self.dec:
            if d.get('target') is not None and 1 <= d['target'] <= self.n:
                labels.add(d['target'])
        junk = set(self.sem.junkops or ())
        body = []
        pendinglocal = {}
        R = lambda d, col: f"R{d['cols'][col]}"
        for d in self.dec:
            i, kind, c = (d['i'], d['kind'], d['cols'])
            if i in labels:
                body.append(f'::L{i}:: ;')
            op = self.P['ops'][i - 1]
            if op in junk and self.afterclosure(i):
                continue
            stmt = self.stmt(d)
            if stmt:
                body.append('  ' + stmt)
        return body

    def afterclosure(self, i):
        if i < 2:
            return False
        prev = self.byi.get(i - 1)
        while prev is not None:
            if prev['kind'] in ('CLOSURE', 'CLOSURE_SETFIELD'):
                return True
            if prev['kind'] not in ('NOP',):
                return False
            prev = self.byi.get(prev['i'] - 1)
        return False

    def kq(self, d, k=0):
        v = self.K(d, k)
        return q2(v) if v is not None else 'nil'

    def stmt(self, d):
        i, kind, c = (d['i'], d['kind'], d['cols'])
        A, B, C, D, E, F, G, H = c
        sbx = d.get('sbx')
        tgt = d.get('target')
        S = None
        if kind == 'NOP':
            return None
        if kind == 'MOVE':
            S = f'R{A} = R{B}'
        elif kind == 'MOVE2':
            S = f'R{A} = R{B}; R{C} = R{D}'
        elif kind == 'MOVE_LOADK':
            S = f'R{A} = R{B}; R{C} = {self.kq(d)}'
        elif kind == 'MOVE_TEST':
            S = f'R{A} = R{B}'
            body.append(None) if False else None
            S = f'R{A} = R{B}; if not R{A} then goto L{tgt} end' if tgt else f'R{A} = R{B}'
        elif kind == 'LOADK':
            S = f'R{A} = {self.kq(d)}'
        elif kind == 'LOADN16':
            S = f'R{A} = {(sbx if sbx is not None else B + C * 256)}'
        elif kind == 'LOADN16_2':
            v1 = B + C * 256
            v1 = v1 - 65536 if v1 >= 32768 else v1
            v2 = E + F * 256
            v2 = v2 - 65536 if v2 >= 32768 else v2
            S = f'R{A} = {v1}; R{D} = {v2}'
        elif kind == 'LOADN32':
            v = B + C * 256 + D * 65536 + E * 16777216
            if v >= 2147483648:
                v -= 4294967296
            S = f'R{A} = {v}'
        elif kind == 'LOADF32':
            v = B + C * 256 + D * 65536 + E * 16777216
            sign = -1 if v >> 31 & 1 else 1
            exp = v >> 23 & 255
            mant = v & 8388607
            if exp == 255:
                val = 0.0
            elif exp == 0:
                val = sign * (mant / 8388608.0) * 2.0 ** (-126)
            else:
                val = sign * (1.0 + mant / 8388608.0) * 2.0 ** (exp - 127)
            S = f'R{A} = {val!r}'
        elif kind == 'LOADNUM':
            S = f'R{A} = {self.kq(d)}'
        elif kind == 'LOADBOOL':
            S = f"R{A} = ({('true' if B != 0 else 'false')})"
        elif kind == 'BOOL_TEST':
            S = f"R{A} = {('true' if B != 0 else 'false')}"
            if tgt:
                S += f'; if not R{A} then goto L{tgt} end'
        elif kind == 'BOOL_JMP':
            S = f"R{C} = {('true' if D != 0 else 'false')}"
            if tgt:
                S += f'; goto L{tgt}'
        elif kind == 'LOADNIL':
            S = f'R{A} = nil'
        elif kind == 'LOADNIL_MASK':
            mask = B + C * 256 + D * 65536 + E * 16777216
            parts = [f'R{A + k} = nil' for k in range(32) if mask & 1 << k]
            S = '; '.join(parts) if parts else None
        elif kind == 'GETGLOBAL':
            S = f'R{A} = _G[{self.kq(d)}]'
        elif kind == 'SETGLOBAL':
            S = f'_G[{self.kq(d)}] = R{A}'
        elif kind == 'GETIMPORT2':
            S = f'R{A} = _G[{self.kq(d, 0)}][{self.kq(d, 1)}]'
        elif kind == 'GETIMPORT3':
            S = f'R{A} = _G[{self.kq(d, 0)}][{self.kq(d, 1)}][{self.kq(d, 2)}]'
        elif kind == 'GETIMPORT_DOTTED':
            S = f'R{A} = _G[{self.kq(d)}] -- dotted import'
        elif kind == 'GETTABLEK':
            S = f'R{A} = R{B}[{self.kq(d)}]'
        elif kind == 'GETTABLEK2':
            S = f'R{A} = R{C}[{self.kq(d, 0)}]; R{B} = R{A}[{self.kq(d, 1)}]'
        elif kind == 'GETTABLEK_SETTABLEK':
            S = f'R{A} = R{B}[{self.kq(d, 0)}]; R{C}[{self.kq(d, 1)}] = R{A}'
        elif kind == 'GETTABLE_RR':
            S = f'R{A} = R{B}[R{C}]'
        elif kind == 'GETTABLE_INT':
            m = re.search('=@(\\d)\\[PC\\]\\+(\\d+)', self.sem.ops[self.P['ops'][i - 1]]['nb'])
            add = int(m.group(2)) if m else 1
            S = f'R{A} = R{B}[{(c[int(m.group(1))] + add if m else C + 1)}]'
        elif kind == 'SETTABLE_RR':
            S = f'R{B}[R{C}] = R{A}'
        elif kind == 'SETTABLE_INT':
            S = f'R{A}[R{B} + 1] = R{C}'
        elif kind == 'SETTABLEK':
            S = f"R{A}[{self.kq(d)}] = {(self.kq(d, 1) if len(d.get('consts', [])) > 1 else 'R' + str(D))}"
        elif kind == 'SETTABLEK_REGVAL':
            S = f'R{A}[{self.kq(d)}] = R{D}'
        elif kind == 'SETTABLEK2':
            S = f'R{A}[{self.kq(d, 0)}] = {self.kq(d, 1)!r}; R{D} = {self.kq(d, 1)!r}'
        elif kind == 'SELF':
            S = f'R{A} = R{B}[{self.kq(d)}]; R{A + 1} = R{B}'
        elif kind == 'ARITH':
            opch = self.arithop(i)
            S = f'R{A} = R{B} {opch} R{C}'
        elif kind == 'ARITH_CONST':
            opch = self.arithop(i)
            v = self.K(d, 0)
            S = f'R{A} = R{B} {opch} {(q2(v) if v is not None else self.kq(d, 1))}'
        elif kind in ('ARITH_SBX', 'ARITH_SWAP'):
            opch = self.arithop(i)
            v = sbx if sbx is not None else 0
            if E and kind == 'ARITH_SWAP':
                S = f'R{A} = R{B} {opch} {v}'
            else:
                S = f'R{A} = R{B} {opch} {v}'
        elif kind == 'IDIV':
            S = f'R{A} = R{B} // R{C}'
        elif kind == 'CONCAT':
            S = f'R{A} = ' + '..'.join((f'R{k}' for k in range(B, C + 1)))
        elif kind == 'LEN':
            S = f'R{A} = #R{B}'
        elif kind == 'NOT':
            S = f'R{A} = not R{B}'
        elif kind == 'NEG':
            S = f'R{A} = -R{B}'
        elif kind == 'AND':
            S = f'R{A} = R{B} and R{C}'
        elif kind == 'OR':
            S = f'R{A} = R{B} or R{C}'
        elif kind == 'GETUPVAL':
            S = f'R{A} = U{B}' if kind == 'GETUPVAL' else None
        elif kind == 'SETUPVAL':
            S = f'U{B} = R{A}'
        elif kind == 'GETUPVAL_GETTABLEK':
            S = f'R{A} = U{E}[{self.kq(d)}]'
        elif kind == 'UPV_GETTABLEK_SET':
            S = f'R{A} = U{E}[{self.kq(d, 0)}]; U{F}[{self.kq(d, 1)}] = R{A}'
        elif kind == 'UPV_GETTABLEK_TEST':
            S = f'R{A} = U{B}[{self.kq(d)}]'
            if tgt:
                S += f'; if not R{A} then goto L{tgt} end'
        elif kind == 'GETTABLEK_TEST':
            S = f'R{A} = R{B}[{self.kq(d)}]'
            if tgt:
                S += f'; if not R{A} then goto L{tgt} end'
        elif kind == 'TEST':
            if d.get('extra', {}).get('pol') == 'truthy' or True:
                S = f'if not R{A} then goto L{tgt} end' if tgt else None
        elif kind == 'JMP':
            S = f'goto L{tgt}' if tgt else None
        elif kind == 'CMP':
            op = self.sem.ops[self.P['ops'][i - 1]].get('extra', {}).get('op', '==')
            rhs = f'R{D}'
            S = f'if R{A} {op} {rhs} then goto L{tgt} end' if tgt else None
        elif kind == 'CMP_CONST':
            op = self.sem.ops[self.P['ops'][i - 1]].get('extra', {}).get('op', '~=')
            S = f'R{B} = {self.kq(d)}'
            if tgt:
                S += f'; if R{A} {op} R{B} then goto L{tgt} end'
        elif kind == 'FORPREP':
            S = f'for R{A} = R{A + 1 or 0}, R{A} , R{A + 1} do end -- FORPREP target={tgt} sbx={sbx}'
        elif kind == 'FORLOOP':
            S = f'-- FORLOOP A={A} target={tgt} sbx={sbx}'
        elif kind == 'TFORPREP':
            S = f'-- TFORPREP A={A} target={tgt}'
        elif kind == 'TFORLOOP':
            S = f'-- TFORLOOP A={A} target={tgt}'
        elif kind == 'CALL':
            base = A
            nargs, nrets = (B, C)
            if nargs == 0:
                args = f'table.unpack(R, {base + 1}, _top - 1)' if False else f'...args'
                args = f'_args(R, {base + 1})'
            else:
                args = ', '.join((f'R{base + k}' for k in range(1, nargs)))
            if nrets == 0:
                S = f'_callm(R, {base}, {nargs})'
            elif nrets == 1:
                S = f'R{base} = R{base}({args})'
            else:
                S = f'R{base}, R{base + 1} = R{base}({args})' if nrets == 2 else f'_retm(R, {base}, R{base}({args}), {nrets})'
        elif kind in ('CALL_GLOBAL', 'CALL_CONST', 'CALL_SELF', 'CALL_UPVAL', 'CALL_TABLEK'):
            base = A
            nargs, nrets = (B, C)
            if kind == 'CALL_GLOBAL':
                callee = f'_G[{self.kq(d)}]'
            elif kind == 'CALL_CONST':
                callee = self.kq(d)
                callee = q2(callee) if isinstance(callee, str) else str(callee)
            elif kind == 'CALL_SELF':
                callee = f'R{base + 1}'
                args = self.kq(d, 0)
                a1 = f'{self.kq(d, 0)!r}'
                if nargs and nargs > 1:
                    rest = ', '.join((f'R{base + k}' for k in range(2, nargs)))
                    args = f'{a1}, {rest}'
                else:
                    args = a1
                if nrets == 0:
                    return f'{callee}:{meth(self, d)}(...)' if False else None
                S = f'R{base} = {callee}[{self.kq(d, 0)!r}]({args})'
                if nrets == 0:
                    S = f'{callee}[{self.kq(d, 0)!r}]({args})'
                return S
            else:
                callee = f'R{base}'
            args = ', '.join((f'R{base + k}' for k in range(1, nargs))) if nargs else ''
            if nrets == 0:
                S = f'{callee}({args})'
            elif nrets == 1:
                S = f'R{base} = {callee}({args})'
            else:
                S = f'R{base}, R{base + 1} = {callee}({args})' if nrets == 2 else f'_retm(R, {base}, {callee}({args}), {nrets})'
        elif kind == 'RETURN':
            if B == 0:
                S = 'return ...'
            elif B == 1:
                S = 'return'
            else:
                S = f"return {', '.join((f'R{A + k}' for k in range(B - 1)))}"
        elif kind == 'CLOSURE':
            S = f'R{A} = _closure[{B + C * 256}]'
        elif kind == 'CLOSURE_SETFIELD':
            S = f'R{D}[{self.kq(d, 0)!r}] = _closure[{E + F * 256}]'
        elif kind == 'CLOSE':
            S = f'-- close upvalues >= {A}'
        elif kind == 'NEWTABLE':
            S = f'R{A} = {{}}'
        elif kind == 'NEWTABLE_KEYS':
            klist = self.sem.keylists.get(0)
            kl = None
            cv = d.get('consts', [])
            if cv:
                pass
            S = f'R{A} = {{}}'
        elif kind == 'NEWTABLE_KEYS_CONST':
            S = f'R{A} = {{}}  -- const table'
        elif kind == 'SETLIST':
            S = f'-- setlist R{A} from R{B}'
        elif kind == 'VARARG_PREP':
            S = f'local _va = table.pack(...)'
        elif kind == 'VARARG_EXPAND':
            S = f'R{A}, R{A + 1} = ...' if B == 2 else f'-- vararg expand A={A} n={B}'
        elif kind == 'LOADLIB':
            fn = loadlibtable.get(A, f'libfn_{A}')
            S = f'-- R{A} = {fn}'
        elif kind == 'GETUPVAL_GETTABLEK_SET':
            S = f'R{A} = U{B}[{self.kq(d, 0)}]'
        else:
            S = f'-- unhandled {kind}'
        return S

    def arithop(self, i):
        nb = self.sem.ops[self.P['ops'][i - 1]]['nb']
        m = re.search('R\\[@0\\[PC\\]\\]=\\(?R\\[@1\\[PC\\]\\]\\)?([-+*/%^])', nb) or re.search('R\\[@0\\[PC\\]\\]=\\w+([-+*/%^])\\w+', nb)
        return m.group(1) if m else '+'

def liftproto(sem, P, protos):
    pl = protolifter(sem, P, protos)
    body = pl.lift()
    name = f"P{P['pid']}"
    params = ', '.join((f'R{k}' for k in range(P['numparams']))) or ''
    if P['is_vararg']:
        params = params + ', ...' if params else '...'
    nup = len(P.get('upvals', []))
    ups = ', '.join((f'U{k}' for k in range(nup)))
    head = f'local function {name}({params})'
    regdecl = '  local ' + ', '.join((f'R{k}' for k in range(P['numparams'], min(60, max(32, P['n'] + 8))))) + ('; ' + ('local ' + ', '.join((f'U{k}' for k in range(nup))) if nup else '') if False else '')
    return (name, head, body, nup)

def liftscript(sem):
    vm = sem.vm
    out = []
    out.append('-- Recovered by wynfuscate_deobfuscator.py (first-pass devirtualization)')
    out.append('-- Structure: one function per VM prototype; goto-style control flow.')
    out.append('local _G = getfenv and getfenv() or _G')
    out.append('local unpack = unpack or table.unpack')
    out.append('local _args, _retm')
    out.append('do')
    out.append('  local function rng(t, a, b)')
    out.append('    local o = {}')
    out.append('    for k = a, b do o[#o + 1] = t[k] end')
    out.append('    return o')
    out.append('  end')
    out.append('  _args = rng')
    out.append('  function _retm(t, base, res, n)')
    out.append('    if n == 1 then t[base] = res; return end')
    out.append('    for k = 1, n do t[base + k - 1] = res[k] end')
    out.append('  end')
    out.append('end')
    names = []
    for P in vm.protos:
        try:
            name, head, body, nup = liftproto(sem, P, vm.protos)
        except Exception:
            continue
        names.append((P, name))
        out.append('')
        params = ', '.join((f'R{k}' for k in range(P['numparams']))) or ''
        if P['is_vararg']:
            params = params + ', ...' if params else '...'
        out.append(f"local {name}  -- proto {P['pid']}: {P['n']} instrs, upvals={len(P.get('upvals', []))}")
    out.append('')
    out.append('-- bodies (forward-declared to allow mutual references)')
    for P, name in names:
        try:
            pl = protolifter(sem, P, vm.protos)
            body = pl.lift()
        except Exception:
            continue
        params = ', '.join((f'R{k}' for k in range(P['numparams']))) or ''
        if P['is_vararg']:
            params = params + ', ...' if params else '...'
        ups = ''
        nu = len(P.get('upvals', []))
        out.append(f'do local function _f({params})')
        out.append('  local ' + ', '.join((f'R{k}' for k in range(P['numparams'], min(64, max(48, P['n'] + 16))))))
        out.extend(('  ' + b if b is not None else '' for b in body))
        out.append('end')
        out.append(f'{name} = _f end')
    out.append('')
    out.append('return P0(...)')
    return '\n'.join((l for l in out if l is not None)) + '\n'
