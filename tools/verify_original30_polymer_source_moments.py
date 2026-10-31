#!/usr/bin/env python3
"""Audit one log-source-to-moment theorem; do not promote original environment 30."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/original30-polymer-source-moments-20261031'
MODULE = 'YMOriginal.Original30_PolymerSourceMoments'
SOURCE = Path(MODULE.replace('.', '/') + '.lean')
NAME = 'YMUIC.Original30.polymer_source_normalized_moments'
PIN = '516d31250e96c4e8e76888c3d8e2e43a9642b9ee'


def main():
    OUT.mkdir(parents=True, exist_ok=True)

    def run(args, name):
        start = time.monotonic()
        result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (OUT / name).write_text(result.stdout)
        if result.returncode:
            raise RuntimeError(f'{name}: exit {result.returncode}\n{result.stdout}')
        return {'command': args, 'exit_code': result.returncode,
                'seconds': round(time.monotonic() - start, 3), 'log': name}

    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    assert 'version 4.35.0-rc3,' in version, version
    pin = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages/mathlib'),
                                   'rev-parse', 'HEAD'], text=True).strip()
    assert pin == PIN, pin
    checks = [run(['lake', 'build', MODULE], 'build.log')]
    audit = OUT / 'ExactTypeAndAxioms.lean'
    audit.write_text(f'import {MODULE}\nset_option pp.all true\n'
                     f'set_option pp.maxSteps 10000000\n'
                     f'#check @{NAME}\n#print axioms {NAME}\n')
    checks.append(run(['lake', 'env', 'lean', '-DwarningAsError=true',
                       str(audit.relative_to(ROOT))], 'exact-type-axioms.log'))
    logpath = OUT / 'exact-type-axioms.log'
    log = logpath.read_text()
    assert 'sorryAx' not in log and '⋯' not in log and '...' not in log
    matches = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    assert len(matches) == 1 and matches[0][0] == NAME, matches
    axioms = [re.sub(r'\.\{[^}]*\}', '', x.strip())
              for x in matches[0][1].split(',') if x.strip()]
    assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
    (OUT / 'exact-type-axioms.log.gz').write_bytes(gzip.compress(logpath.read_bytes(), mtime=0))
    logpath.unlink()
    checks[-1]['log'] = 'exact-type-axioms.log.gz'
    checks.append(run(['lake', 'env', 'leanchecker', '-v', MODULE], 'kernel-replay.log'))

    hashes = {}

    def visit(path):
        if str(path) in hashes:
            return
        content = (ROOT / path).read_text()
        assert not re.search(r'^\s*(?:axiom|unsafe|partial)\b', content, re.M)
        assert not re.search(r'\b(?:sorry|admit)\b', content)
        hashes[str(path)] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for module in re.findall(r'^import\s+(\S+)', content, re.M):
            if module.startswith(('YM.', 'YMOriginal.', 'YMConditional.')):
                visit(Path(module.replace('.', '/') + '.lean'))

    visit(SOURCE)
    summary = {
        'status': 'PASS_ANALYTIC_LOG_SOURCE_TO_FULL_MOMENTS',
        'theorem': NAME, 'lean': version, 'mathlib': PIN,
        'checks': checks, 'source_sha256': hashes, 'axioms': axioms,
        'bound': 'e * r! * (e * (1 + 2*A) / rho)^r * product_j norm(h_j)',
        'orders': 'all natural r, including zero',
        'generating_function': 'Z(J) = exp(sum_Gamma activity_i(J) - sum_Gamma activity_i(0))',
        'inputs': ['0 < rho', '0 <= A', 'each activity analytic on the rho source ball',
                   'each activity bounded there by weight_i', 'sum_Gamma weight_i <= A'],
        'original_environment_30': 'OPEN: physical renormalized-source identification, uniform input budgets, joint Schwartz extension and continuum passage',
        'original_environment_24': 'OPEN: unchanged',
        'original_conditional_ledger': '37/39 unchanged',
        'I7': 'explicit unproved global hypothesis',
    }
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'status': summary['status'], 'axioms': axioms,
                      'original_conditional_ledger': summary['original_conditional_ledger']}))


if __name__ == '__main__':
    main()
