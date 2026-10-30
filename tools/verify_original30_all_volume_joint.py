#!/usr/bin/env python3
"""Compile and replay the bare joint source estimate; original #30 stays open."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/original30-all-volume-joint-20261031'
SOURCE = ROOT / 'YMOriginal/Original30_AllVolumeJointSchwartz.lean'
MODULE = 'YMOriginal.Original30_AllVolumeJointSchwartz'
PIN = '516d31250e96c4e8e76888c3d8e2e43a9642b9ee'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    def run(args, name):
        start = time.monotonic()
        p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
        (OUT / name).write_text(p.stdout)
        if p.returncode:
            raise RuntimeError(f'{name}: exit {p.returncode}\n{p.stdout}')
        return {'command': args, 'exit_code': p.returncode,
                'seconds': round(time.monotonic() - start, 3), 'log': name}
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    assert 'version 4.35.0-rc3,' in version, version
    pin = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages/mathlib'),
                                   'rev-parse', 'HEAD'], text=True).strip()
    assert pin == PIN, pin
    checks = [run(['lake', 'build', MODULE], 'build.log')]
    names = re.findall(r'^(?:def|theorem) (\w+)', SOURCE.read_text(), re.M)
    assert len(names) == 5, names
    fullnames = ['YMUIC.Original30.' + n for n in names]
    audit = ['import ' + MODULE, 'set_option pp.all true',
             'set_option pp.maxSteps 10000000']
    for n in fullnames:
        audit += ['#check @' + n, '#print axioms ' + n]
    audit_path = OUT / 'ExactTypesAndAxioms.lean'
    audit_path.write_text('\n'.join(audit) + '\n')
    checks.append(run(['lake', 'env', 'lean', '-DwarningAsError=true',
                       str(audit_path.relative_to(ROOT))], 'exact-types-axioms.log'))
    logpath = OUT / 'exact-types-axioms.log'
    log = logpath.read_text()
    assert 'sorryAx' not in log and '⋯' not in log and '...' not in log
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    receipts = {}
    for n, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S):
        axioms = [re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in raw.split(',') if x.strip()]
        assert set(axioms) <= allowed, (n, axioms)
        receipts[n] = axioms
    for n in re.findall(r"'([^']+)' does not depend on any axioms", log):
        receipts[n] = []
    assert set(receipts) == set(fullnames), receipts
    (OUT / 'exact-types-axioms.log.gz').write_bytes(gzip.compress(logpath.read_bytes(), mtime=0))
    logpath.unlink()
    checks[-1]['log'] = 'exact-types-axioms.log.gz'
    checks.append(run(['lake', 'env', 'leanchecker', '-v', MODULE], 'kernel-replay.log'))
    hashes = {}
    def visit(path):
        if str(path) in hashes:
            return
        text = (ROOT / path).read_text()
        hashes[str(path)] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for mod in re.findall(r'^import\s+(\S+)', text, re.M):
            if mod.startswith(('YM.', 'YMOriginal.', 'YMConditional.')):
                visit(Path(mod.replace('.', '/') + '.lean'))
    visit(SOURCE.relative_to(ROOT))
    summary = {
        'status': 'PASS_BARE_JOINT_ESTIMATE_ONLY',
        'lean': version, 'mathlib': PIN, 'checks': checks,
        'source_sha256': hashes, 'axioms': receipts,
        'new_main_estimate': 'actual_word_joint_probability_all_volume',
        'scope': 'all r, all N, 0<a<=1; full joint Schwartz test at actual nonnegative grid sites',
        'bound': '(24576*K)^r * (p_(0,0)(F) + p_(8r,0)(F))',
        'original_environment_30': 'OPEN: renormalized source/counterterm and continuum dictionary absent',
        'original_environment_24': 'OPEN: no change',
        'original_conditional_ledger': '37/39 unchanged',
        'I7': 'explicit unproved global hypothesis',
        'interface_warning': 'existing OS_E0prime uses fixed spatial q; this result uses spatial 8*r; no conversion claimed',
    }
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'status': summary['status'], 'audited_declarations': len(receipts),
                      'original_conditional_ledger': summary['original_conditional_ledger']}))

if __name__ == '__main__':
    main()
