#!/usr/bin/env python3
"""Audit common cluster limits of the actual bounded Wilson source family."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification/original30-source-cluster-20261031'
TARGETS = {
    'YMOriginal.Original30_JointUltrafilterCompactness':
        'YMUIC.Original30.joint_ultrafilter_compactness',
    'YMOriginal.Original30_ActualSourceClusterHierarchy':
        'YMUIC.Original30.actual_source_cluster_hierarchy',
    'YMOriginal.Original30_ActualSourceDiagonalLimit':
        'YMUIC.Original30.actual_source_diagonal_limit',
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
                               for n in TARGETS.values()) + '\n' +
                     '#print YMUIC.Original30.actualWilsonGeneratingFunction\n' +
                     '#print YMUIC.Original30.actualWilsonSourceJointDistribution\n' +
                     '#print YMUIC.Original30.wilsonDiagonalSpacing\n' +
                     '#print YMUIC.Original30.wilsonDiagonalSize\n')
    log = run(['lake', 'env', 'lean', '-DwarningAsError=true',
               str(audit.relative_to(ROOT))], 'exact-types-axioms.log')
    assert not any(marker in log for marker in ('sorryAx', '⋯', '...'))
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.S)
    assert set(n for n, _ in found) == set(TARGETS.values()) and len(found) == len(TARGETS)
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
        source = (ROOT / (module.replace('.', '/') + '.lean')).read_text()
        assert len(re.findall(r'^\s*(?:theorem|lemma)\s', source, re.M)) == 1
        visit(module)
    summary = {
        'status': 'PASS_ACTUAL_SOURCE_COMMON_CLUSTER_LIMIT',
        'lean': version, 'mathlib': pin, 'checks': checks,
        'theorems': list(TARGETS.values()), 'axioms': axiom_map,
        'printed_definitions': ['YMUIC.Original30.actualWilsonGeneratingFunction',
                                'YMUIC.Original30.actualWilsonSourceJointDistribution',
                                'YMUIC.Original30.wilsonDiagonalSpacing',
                                'YMUIC.Original30.wilsonDiagonalSize'],
        'source_sha256': hashes,
        'derived': [
            'one ultrafilter refines any prescribed nontrivial regulator filter',
            'simultaneous convergence for all orders and all joint Schwartz tests',
            'linearity and continuity of the limit hierarchy',
            'unchanged factorial and joint Schwartz seminorm bounds',
            'actual source limit normalization H.S 0 f = f 0',
            'explicit a_n = 1/(n+1), N_n = (n+1)^2: a_n -> 0, a_n*N_n -> infinity',
            'uniqueness of the hierarchy for the selected ultrafilter'],
        'inputs': [
            'continuous SU(2) link coordinates at each regulator',
            'regulator-dependent probability laws and configuration spaces',
            '0 < a_i <= 1 for the arbitrary-regulator theorem',
            'one common Wilson polynomial coefficient budget K'],
        'not_derived': [
            'uniform physical renormalized coefficient budget',
            'physical RG source or nonlinear counterterm identification',
            'convergence along the original regulator filter',
            'uniqueness independent of the selected ultrafilter',
            'nontriviality, Euclidean covariance or reflection positivity of the limit',
            'fixed-q OS_E0prime or a full physical Yang-Mills continuum hierarchy'],
        'original_environment_30': 'OPEN',
        'original_conditional_ledger': '37/39 unchanged',
        'I7': 'explicit unproved premise',
    }
    (OUT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'status': summary['status'], 'axioms': axiom_map,
                      'original_conditional_ledger': summary['original_conditional_ledger']}))


if __name__ == '__main__':
    main()
