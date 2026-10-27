from __future__ import annotations
import argparse
from pathlib import Path as pth
from . import version
from .util import readtext
from .prelude import stage1strings
from .packer import unpackenhancedvm
from .vm import vmdeobf
from .semant import semantics
from .decode import disasm
from .lift import liftscript
from .structure import liftscriptgen2
from .polish import polish

def iswynfuscate(src: str) -> bool:
    return 'wYnFuscate' in src or 'wynfuscate' in src.lower()

def lookstruncated(src: str):
    tail = src.rstrip()[-60:]
    if tail.endswith('end') or tail.endswith(')') or tail.endswith('end)') or tail.endswith('else'):
        return None
    return tail

def deobfuscate(path: pth, outdir: pth, nopolish: bool=False):
    src = readtext(path)
    print(f'\n=== {path.name} ({len(src)} chars) ===')
    outdir.mkdir(parents=True, exist_ok=True)
    stem = path.stem
    if not iswynfuscate(src):
        print('  ! not a wYnFuscate protected script')
        return
    report = [f'# wYnFuscate deobfuscation report - {path.name}', f'produced by wynfuscate_deobfuscator.py v{version} (python3 wynfuscate_deobfuscator.py --version to check your copy)', '']
    notes = []
    inner = unpackenhancedvm(src)
    if inner:
        (outdir / f'{stem}.layer2_inner.lua').write_text(inner, encoding='utf-8')
        report.append(f'* layer 2 **enhanced-vm-compress** wrapper unpacked -> `{stem}.layer2_inner.lua` ({len(inner)} chars)')
        src = inner
    else:
        report.append('* layer 2: not present')
    s1 = stage1strings(src)
    if s1:
        strings, info = s1
        report.append(f"* layer 1 bootstrap strings: **{len(strings)}** recovered (pool {info['pool_len']} bytes, seed {info['seed']})")
        with (outdir / f'{stem}.bootstrap_strings.txt').open('w', encoding='utf-8') as f:
            for k in sorted(strings):
                v = strings[k]
                v = v.decode('utf-8', errors='replace') if isinstance(v, bytes) else v
                f.write(f'[{k}] {v}\n')
    else:
        report.append('* layer 1: no bootstrap string table')
    vm = vmdeobf(src)
    ok = False
    try:
        ok = vm.parse()
    except Exception as e:
        report.append(f'* layers 3-5: failed ({e!r})')
        notes.append(f'VM parse error: {e!r}')
    if ok:
        if vm.strings:
            report.append(f'* layer 3 VM string table: **{len(vm.strings)}** strings recovered')
            with (outdir / f'{stem}.vm_strings.txt').open('w', encoding='utf-8') as f:
                for k in sorted(vm.strings):
                    f.write(f'[{k}] {vm.strings[k]}\n')
        if vm.protos:
            report.append(f"* layer 4 bytecode: WPT{vm.wptversion - 48}, **{len(vm.protos)} prototypes**, {sum((p['n'] for p in vm.protos))} instructions (stream consumed {vm.wptconsumed}/{vm.wpttotal} bytes)")
            report.append(f'* layer 5 dispatch tree: {len(vm.handlers)} opcode handlers extracted')
            lines = vm.instructionlines()
            (outdir / f'{stem}.instructions.txt').write_text('\n'.join(lines), encoding='utf-8')
            report.append(f'* devirtualized instruction listing -> `{stem}.instructions.txt`')
            if getattr(vm, 'g3', False):
                try:
                    from .g3semant import g3sem
                    from .g3lift import g3lifter
                    sem = g3sem(vm)
                    lf = g3lifter(vm, sem)
                    lift = lf.liftscript()
                    (outdir / f'{stem}.deobf.lua').write_text(lift, encoding='utf-8')
                    nl = len(lift.splitlines())
                    used = {}
                    for P in vm.protos:
                        for o in P['ops']:
                            used[o] = used.get(o, 0) + 1
                    report.append(f'* layer 6 opcode semantics: {len(vm.handlers)} handlers decoded symbolically (gen-3 interpreter)')
                    report.append(f'* layer 7-8 devirtualized Lua (gen-3 lift, first pass): {nl} lines -> `{stem}.deobf.lua`')
                except Exception as e:
                    report.append(f'* layer 6/8 gen-3 semantics: failed ({type(e).__name__}: {e})')
            else:
                try:
                    sem = semantics(vm)
                    if not sem.problems or len(sem.problems) <= 1:
                        disparts = []
                        for P in sem.vm.protos:
                            disparts.append(f"===== proto {P['pid']}  (n={P['n']}, params={P['numparams']}, vararg={P['is_vararg']}, upvals={len(P.get('upvals', []))}) =====")
                            disparts.append(disasm(sem, P))
                            disparts.append('')
                        (outdir / f'{stem}.disassembly.txt').write_text('\n'.join(disparts), encoding='utf-8')
                        report.append(f'* semantic disassembly ({len(sem.vm.protos)} protos, doubles pool {len(sem.doubles)}) -> `{stem}.disassembly.txt`')
                        used = {}
                        for P in sem.vm.protos:
                            for o in P['ops']:
                                used[o] = used.get(o, 0) + 1
                        unk = sum((c for o, c in used.items() if sem.ops.get(o, {}).get('kind') in ('UNKNOWN',)))
                        tot = sum(used.values())
                        report.append(f"* opcode classification: {tot - unk}/{tot} instructions mapped to {len(set((s.get('kind') for s in sem.ops.values())))} semantic forms" + ('' if unk == 0 else f' ({unk} unclassified)'))
                        try:
                            lift = liftscriptgen2(sem)
                            polished = None
                            if not nopolish:
                                try:
                                    polished = polish(lift)
                                except Exception as pe:
                                    report.append(f'* stage-8 polish skipped ({type(pe).__name__}: {pe}); unpolished lift kept')
                            if polished is not None:
                                (outdir / f'{stem}.deobf.lua').write_text(polished, encoding='utf-8')
                                report.append(f'* devirtualized Lua (gen-2 lift + stage-8 polish: {len(lift.splitlines())} -> {len(polished.splitlines())} lines) -> `{stem}.deobf.lua`')
                            else:
                                (outdir / f'{stem}.deobf.lua').write_text(lift, encoding='utf-8')
                                report.append(f'* devirtualized Lua (runnable gen-2 lift) -> `{stem}.deobf.lua`')
                        except Exception as e:
                            try:
                                lift = liftscript(sem)
                                (outdir / f'{stem}.deobf.lua').write_text(lift, encoding='utf-8')
                                report.append(f'* devirtualized Lua (first-pass lift; gen-2 failed: {type(e).__name__}: {e}) -> `{stem}.deobf.lua`')
                            except Exception as e2:
                                report.append(f'* lift failed: gen2 {e!r}; legacy {e2!r}')
                except Exception as e:
                    report.append(f'* semantic devirtualization failed: {e!r}')
        elif vm.wptversion is not None:
            report.append(f'* layer 4: WPT version {vm.wptversion - 48} not supported for listing')
    else:
        trunc = lookstruncated(src)
        if trunc is not None:
            notes.append(f'the file appears to be **truncated** -- it ends mid-statement with ...{trunc[-40:]!r} after only {len(src)} characters. Everything after this point in a complete build (the VM string table and the bytecode -- i.e. the actual payload) is missing, so only the layers above could be recovered. Complete wYn builds are typically 30 KB to 300+ KB; re-export the full file and re-run.')
        if s1 is None and inner is None:
            notes.append('only the environment-resolution prelude is present; there is no protected payload in this file (most likely an incomplete export).')
    for w in vm.warnings:
        notes.append(w)
    if notes:
        report += ['', '## Notes']
        report += [f'- {n}' for n in notes]
    (outdir / f'{stem}.report.md').write_text('\n'.join(report) + '\n', encoding='utf-8')
    for line in report:
        if line.startswith('* '):
            print('  ' + line[2:])
    for n in notes:
        print(f'  note: {n[:140]}')
    print(f'  -> {outdir}/{stem}.report.md')

def main():
    ap = argparse.ArgumentParser(description='static wYnFuscate deobfuscator')
    ap.add_argument('--version', action='version', version='wynfuscate_deobfuscator %s' % version)
    ap.add_argument('files', nargs='*', type=pth)
    ap.add_argument('-o', '--outdir', type=pth, default=pth('wynfuscate_deobf'))
    ap.add_argument('--no-polish', action='store_true', help='skip the stage-8 readability polish (keep raw gen-2 lift)', dest='nopolish')
    args = ap.parse_args()
    if not args.files:
        ap.print_usage()
        print('\nno input files given.')
        print('usage: python wynfuscate_deobfuscator.py FILE [FILE ...] [-o OUTDIR] [--no-polish]')
        return 1
    print('wynfuscate_deobfuscator %s' % version)
    for f in args.files:
        if not f.exists():
            print(f'!! {f} not found')
            continue
        try:
            deobfuscate(f, args.outdir, nopolish=args.nopolish)
        except Exception as e:
            print(f'!! {f}: {e!r}')
