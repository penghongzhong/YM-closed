#!/usr/bin/env python3
"""Audit the dense-test/common-filter limit bridge; no original-environment promotion."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/original30-atom-limit-20261031'
TARGETS = {
    'YMOriginal.Original30_DenseTestLimit':
        'YMUIC.Original30.dense_test_same_filter_limit',
    'YMOriginal.Original30_AtomHierarchyLimit':
        'YMUIC.Original30.joint_atom_same_filter_limit',
}
PIN = '516d31250e96c4e8e76888c3d8e2e43a9642b9ee'


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    checks = []

    def run(args, name):
        start = time.monotonic()
        result = subprocess.run(args, cwd=ROOT, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (OUT / name).write_text(result.stdout)
        checks.append({'command': args, 'exit_code': result.returncode,
                       'seconds': round(time.monotonic() - start, 3), 'log': name})
        if result.returncode:
            raise RuntimeError(f'{name}: exit {result.returncode}\n{result.stdout}')
        return result.stdout

    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    assert 'version 4.35.0-rc3,' in version, version
    pin = subprocess.check_output(['git', '-C', str(ROOT / '.lake/packages/mathlib'),
                                   'rev-parse', 'HEAD'], text=True).strip()
    assert pin == PIN, pin
    run(['lake', 'build', *TARGETS], 'build.log')
    audit = OUT / 'ExactTypesAndAxioms.lean'
    audit.write_text('\n'.join(f'import {m}' for m in TARGETS) +
                     '\nset_option pp.all true\nset_option pp.maxSteps 10000000\n' +
                     '\n'.join(f'#check @{n}\n#print axioms {n}'
                               for n in TARGETS.values()) + '\n')
    log = run(['lake', 'env', 'lean', '-DwarningAsError=true',
               str(audit.relative_to(ROOT))], 'exact-types-axioms.log')
    assert not any(marker in log for marker in ('sorryAx', '⋯', '...'))
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    assert set(n for n, _ in found) == set(TARGETS.values()) and len(found) == 2
    axiom_map = {}
    for name, raw in found:
        axioms = [re.sub(r'\.\{[^}]*\}', '', a.strip())
                  for a in raw.split(',') if a.strip()]
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, axioms
        axiom_map[name] = axioms
    path = OUT / 'exact-types-axioms.log'
    path.with_suffix('.log.gz').write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    path.unlink()
    checks[-1]['log'] = 'exact-types-axioms.log.gz'
    for index, module in enumerate(TARGETS):
        run(['lake', 'env', 'leanchecker', '-v', module], f'kernel-{index}.log')

    hashes = {}

    def visit(module):
        path = Path(module.replace('.', '/') + '.lean')
        if str(path) in hashes:
            return
        data = (ROOT / path).read_bytes()
        content = data.decode()
        assert not re.search(r'^\s*(?:axiom|unsafe|partial)\b', content, re.M)
        assert not re.search(r'\b(?:sorry|admit)\b', content)
        hashes[str(path)] = hashlib.sha256(data).hexdigest()
        for dep in re.findall(r'^import\s+(\S+)', content, re.M):
            if dep.startswith(('YM.', 'YMOriginal.', 'YMConditional.')):
                visit(dep)

    for module in TARGETS:
        visit(module)
    summary = {
        'status': 'PASS_DENSE_ATOM_COMMON_FILTER_EXTENSION',
        'lean': version, 'mathlib': pin, 'checks': checks,
        'theorems': list(TARGETS.values()), 'axioms': axiom_map,
        'source_sha256': hashes,
        'derived': ['finite-span convergence from atom convergence',
                    'unique continuous joint hierarchy',
                    'convergence on all joint tests along the original filter',
                    'unchanged uniform seminorm bounds'],
        'inputs': ['same nontrivial regulator filter for every order',
                   'density of the chosen atom spans in joint Schwartz topology',
                   'convergence on individual atoms',
                   'regulated joint continuous linear functionals and uniform seminorm bounds'],
        'not_derived': ['physical renormalized source construction',
                       'actual Fourier/pure-tensor atom-span density dictionary',
                       'physical uniform analytic radius and estimates',
                       'actual atom convergence'],
        'original_environment_30': 'OPEN',
        'original_conditional_ledger': '37/39 unchanged',
        'I7': 'explicit unproved premise',
    }
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'status': summary['status'], 'axioms': axiom_map,
                      'original_conditional_ledger': summary['original_conditional_ledger']}))


if __name__ == '__main__':
    main()
