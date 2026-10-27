from __future__ import annotations
import re

def decodeinstruction(sem, P, i):
    op = P['ops'][i - 1]
    o = sem.ops.get(op)
    cols = [P['regs'][c].get(i) or 0 for c in range(8)]
    out = {'i': i, 'op': op, 'kind': o['kind'] if o else 'NOHANDLER', 'cols': cols}
    if o is None:
        return out
    st = o.get('state')

    def ev(sym):
        return sem.evalsym(sym, i, cols)
    kind = o['kind']
    if st is not None:
        writes = st.writes
        out['writes'] = [(ev(w[0]), w[1]) for w in writes]
        out['calls'] = [(c[1], c[2]) for c in st.calls]
    if kind in ('JMP', 'TEST', 'MOVE_TEST', 'BOOL_TEST', 'GETTABLEK_TEST', 'GETUPVAL_GETTABLEK_TEST'):
        out['target'] = P['uk'].get(i)
    elif kind == 'CMP':
        out['target'] = P['ue'].get(i)
    elif kind == 'CMP_CONST':
        out['target'] = P['ue'].get(i)
    elif kind in ('FORPREP', 'FORLOOP', 'TFORLOOP', 'TFORPREP', 'BOOL_JMP'):
        nb = o['nb']
        m = re.search('UF\\[PC\\]\\+(\\d+)\\+\\w+', nb)
        own = int(m.group(1)) if m else 4
        sbx = None
        for m2 in re.finditer('@\\d\\[PC\\]\\+\\(@(\\d)\\[PC\\]\\*256\\)', nb):
            a, b = (None, int(m2.group(1)))
            m3 = re.search('@(\\d)\\[PC\\]\\+\\(@' + str(b) + '\\[PC\\]\\*256\\)', nb)
            if m3:
                lo, hi = (int(m3.group(1)), b)
                v = cols[lo] + cols[hi] * 256
                if v >= 32768:
                    v -= 65536
                sbx = v
                break
        if sbx is None:
            m4 = re.search('=@3\\[PC\\]\\+\\(@4\\[PC\\]\\*256\\)|=@4\\[PC\\]\\+\\(@3', nb)
        out['own_size'] = own
        out['sbx'] = sbx
        if sbx is not None:
            off = P['uf'].get(i)
            if off is not None:
                out['target'] = P['ufx'].get(off + own + sbx)
    return out

def disassemble(sem, P, maxlines=None):
    lines = []
    for i in range(1, P['n'] + 1):
        d = decodeinstruction(sem, P, i)
        cols = d['cols']
        base = f"[{i:4d}] {d['op']:3d} {d['kind']:22s} A={cols[0]:3d} B={cols[1]:3d} C={cols[2]:3d} D={cols[3]:3d}"
        extra = []
        if 'target' in d and d['target'] is not None:
            extra.append(f"-> {d['target']}")
        for w in d.get('writes', []):
            dest, val = w
            extra.append(f'W {dest}={val!r}')
        for c in d.get('calls', []):
            extra.append(f'CALL {c[0]!r}({c[1]!r})')
        lines.append(base + '  ' + ' '.join((str(x) for x in extra)))
        if maxlines and i >= maxlines:
            break
    return '\n'.join(lines)

def extractmasks(nb):
    out = {}
    for m in re.finditer('(\\w+)=\\(\\(PC\\*(\\d+)\\)\\+(\\d+)\\)%(\\d+)', nb):
        out[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    return out

def constspecs(nb):
    masks = extractmasks(nb)
    lazy = {}
    for m in re.finditer('(@\\d)\\[PC\\]=XOR\\(\\((@\\d)\\[PC\\]or 0\\),(\\w+)\\)', nb):
        lazy[m.group(1)] = (m.group(2), m.group(3))
    specs = []
    for m in re.finditer('MAP\\[(\\w+)(\\+(\\d+))?\\]', nb):
        var, add = (m.group(1), int(m.group(3) or 0))
        spec = resolveuc(var, nb, masks, lazy)
        if spec is not None:
            spec['add'] = add
            specs.append(spec)
    for m in re.finditer('POOL\\[(\\w+)\\]', nb):
        spec = resolveuc(m.group(1), nb, masks, lazy)
        if spec is not None:
            specs.append({'kind': 'pool', **spec})
    return specs

def resolveuc(var, nb, masks, lazy):
    m = re.search('(\\w+)=XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\+\\(XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\*(\\d+)\\)', nb)
    while m:
        if m.group(1) == var:
            t1, t2 = (masks.get(m.group(3)), masks.get(m.group(5)))
            if t1 and t2:
                return {'kind': 'inl', 'lo': int(m.group(2)[1:]), 'hi': int(m.group(4)[1:]), 'm1': t1, 'm2': t2, 'mult': int(m.group(6))}
        m = re.search('(\\w+)=XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\+\\(XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\*(\\d+)\\)', nb[m.end():] and nb) if False else None
    for m in re.finditer('(\\w+)=XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\+\\(XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\*(\\d+)\\)', nb):
        if m.group(1) == var:
            t1, t2 = (masks.get(m.group(3)), masks.get(m.group(5)))
            if t1 and t2:
                return {'kind': 'inl', 'lo': int(m.group(2)[1:]), 'hi': int(m.group(4)[1:]), 'm1': t1, 'm2': t2, 'mult': int(m.group(6))}
    for m in re.finditer('(\\w+)=(@\\d)\\[PC\\]\\+\\((@\\d)\\[PC\\]\\*256\\)', nb):
        if m.group(1) == var:
            c1, c2 = (m.group(2), m.group(3))
            if c1 in lazy and c2 in lazy:
                s1, t1 = lazy[c1]
                s2, t2 = lazy[c2]
                mm1, mm2 = (masks.get(t1), masks.get(t2))
                if mm1 and mm2:
                    return {'kind': 'inl', 'lo': int(s1[1:]), 'hi': int(s2[1:]), 'm1': mm1, 'm2': mm2, 'mult': 256}
    for m in re.finditer('(\\w+)=(@\\d)\\[PC\\]\\+\\((@\\d)\\[PC\\]\\*256\\)', nb):
        if m.group(1) == var:
            return {'kind': 'plain', 'lo': int(m.group(2)[1:]), 'hi': int(m.group(3)[1:]), 'mult': 256}
    for m in re.finditer('(\\w+)=(@\\d)\\[PC\\]($|[^([])', nb):
        if m.group(1) == var:
            return {'kind': 'colpair0', 'lo': int(m.group(2)[1:]), 'hi': None, 'mult': 1}
    return None

def sbxpairs(nb):
    out = []
    for m in re.finditer('(@\\d)\\[PC\\]\\+\\((@\\d)\\[PC\\]\\*256\\)', nb):
        out.append((int(m.group(1)[1:]), int(m.group(2)[1:])))
    for m in re.finditer('XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\+\\(XOR\\((@\\d)\\[PC\\],(\\w+)\\)\\*256\\)', nb):
        out.append(None)
        break
    return out

def buildspec(sem, op):
    o = sem.ops[op]
    nb, kind = (o['nb'], o['kind'])
    cspecs = constspecs(nb)
    spec = {'kind': kind, 'consts': cspecs, 'sbx': sbxpairs(nb)}
    stores = re.findall('R\\[@(\\d)\\[PC\\]\\]=', nb)
    spec['dests'] = [int(c) for c in stores]
    return spec

def decodeall(sem, P):
    out = []
    masksof = {}
    for i in range(1, P['n'] + 1):
        op = P['ops'][i - 1]
        o = sem.ops.get(op)
        if o is None:
            out.append({'i': i, 'op': op, 'kind': 'NOHANDLER'})
            continue
        nb, kind = (o['nb'], o['kind'])
        cols = [P['regs'][c].get(i) or 0 for c in range(8)]
        d = {'i': i, 'op': op, 'kind': kind, 'cols': cols}

        def sbx(pair):
            lo, hi = pair
            v = (cols[lo] or 0) + (cols[hi] or 0) * 256
            return v - 65536 if v >= 32768 else v

        def const(k=0):
            if k < len(o.get('cspecs', [])):
                cs = o['cspecs'][k]
                if cs['kind'] == 'inl':
                    m1 = (i * cs['m1'][0] + cs['m1'][1]) % cs['m1'][2]
                    m2 = (i * cs['m2'][0] + cs['m2'][1]) % cs['m2'][2]
                    uc = ((cols[cs['lo']] or 0) ^ m1) + ((cols[cs['hi']] or 0) ^ m2) * cs['mult']
                    uc += cs.get('add', 0)
                    if cs.get('kind') == 'pool' or True:
                        if 0 <= uc - cs.get('add', 0) < 10 ** 9:
                            pass
                    return ('inl', uc)
                if cs['kind'] == 'pool':
                    m1 = (i * cs['m1'][0] + cs['m1'][1]) % cs['m1'][2]
                    m2 = (i * cs['m2'][0] + cs['m2'][1]) % cs['m2'][2]
                    uc = ((cols[cs['lo']] or 0) ^ m1) + ((cols[cs['hi']] or 0) ^ m2) * cs['mult']
                    return ('pool', uc)
                if cs['kind'] == 'plain':
                    uc = (cols[cs['lo']] or 0) + (cols[cs['hi']] or 0) * cs['mult'] + cs.get('add', 0)
                    return ('inl', uc)
            return None
        d['A'], d['B'], d['C'], d['D'], d['E'], d['F'], d['G'], d['H'] = cols
        sp = o.get('spec') or {}
        if 'sbx' in sp and sp['sbx']:
            pair = sp['sbx'][0]
            if pair:
                d['sbx'] = sbx(pair)
        if kind in ('JMP', 'TEST', 'MOVE_TEST', 'BOOL_TEST', 'GETTABLEK_TEST', 'UPV_GETTABLEK_TEST'):
            d['target'] = P['uk'].get(i)
        elif kind in ('CMP', 'CMP_CONST'):
            d['target'] = P['ue'].get(i)
        elif kind in ('FORPREP', 'FORLOOP', 'TFORLOOP', 'TFORPREP', 'BOOL_JMP'):
            m = re.search('UF\\[PC\\]\\+(\\d+)', nb)
            own = int(m.group(1)) if m else 4
            d['own_size'] = own
            if 'sbx' in d and d['sbx'] is not None:
                off = P['uf'].get(i)
                if off is not None:
                    d['target'] = P['ufx'].get(off + own + d['sbx'])
        if o.get('cspecs'):
            d['consts'] = [const(k) for k in range(len(o['cspecs']))]
        out.append(d)
    return out

def resolveconst(sem, c):
    if c is None:
        return None
    tag, uc = c
    if tag == 'pool':
        return sem.doubles.get(uc)
    if 0 <= uc < len(sem.vm.inlinemap):
        sid = sem.vm.inlinemap[uc]
        if sid != 65535:
            return sem.vm.strings.get(sid)
    return None

def disasm(sem, P, limit=None):
    lines = []
    dec = decodeall(sem, P)
    for d in dec:
        c = d['cols']
        parts = [f"[{d['i']:4d}] {d['op']:3d} {d['kind']:20s}"]
        parts.append(f'A={c[0]:3d} B={c[1]:3d} C={c[2]:3d} D={c[3]:3d} E={c[4]:3d} F={c[5]:3d}')
        if 'sbx' in d and d['sbx'] is not None:
            parts.append(f"sbx={d['sbx']}")
        if 'target' in d and d['target'] is not None:
            parts.append(f"-> {d['target']}")
        for cv in d.get('consts', []):
            parts.append(f'K={ascii(resolveconst(sem, cv))}')
        lines.append('  '.join(parts))
        if limit and d['i'] >= limit:
            break
    return '\n'.join(lines)
