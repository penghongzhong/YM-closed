"""Pinned-toolchain raw compilation and axiom audit; no manuscript inputs."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--current', action='store_true')
a = p.parse_args()
root = Path.cwd()
build = root / '.lean-verify'
build.mkdir(exist_ok=True)
env = dict(os.environ)
env['LEAN_PATH'] = str(build) + os.pathsep + env.get('LEAN_PATH', '')
paths = sorted(Path('Lean').rglob('*.lean'))
if a.current:
    paths = [f for f in paths if f.name >= 'T008' and f.name.startswith('T')]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
rows = []
for f in paths:
    print('::group::RAW ' + str(f), flush=True)
    out = build / f.with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(['lean', '-o', str(out), str(f)], env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = proc.stdout
    print(text, end='', flush=True)
    print('RAW_EXIT_CODE=' + str(proc.returncode), flush=True)
    groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
    names = sorted({v.strip() for g in groups for v in g.split(',') if v.strip()})
    forbidden = sorted(set(names) - allowed)
    audits = len(groups) + text.count('does not depend on any axioms')
    needs_audit = bool(re.search(r'^\s*(?:theorem|lemma)\s', f.read_text(), re.M))
    ok = proc.returncode == 0 and not forbidden and 'sorryAx' not in text and (audits > 0 or not needs_audit)
    rows.append({'file': str(f), 'raw_exit_code': proc.returncode, 'axioms': names,
                 'axiom_audits': audits, 'forbidden_axioms': forbidden, 'pass': ok})
    out.with_suffix('.raw.log').write_text(text)
    print('AXIOM_GATE=' + ('PASS' if ok else 'FAIL'), flush=True)
    print('::endgroup::', flush=True)
result = {'head': os.environ.get('GITHUB_SHA', ''), 'files': rows,
          'pass': bool(rows) and all(r['pass'] for r in rows)}
(build / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
sys.exit(0 if result['pass'] else 1)
