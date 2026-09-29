"""Pinned-toolchain raw compilation and axiom audit; no manuscript inputs."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

def code_only(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1; i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1; i += 2
        elif depth:
            i += 1
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            i += 1
            out.append(' ')
        else:
            out.append(text[i]); i += 1
    return ''.join(out)

p = argparse.ArgumentParser()
p.add_argument('--current', action='store_true')
a = p.parse_args()
root = Path.cwd()
build = root / '.lean-verify'
build.mkdir(exist_ok=True)
env = dict(os.environ)
env['LEAN_PATH'] = str(build) + os.pathsep + env.get('LEAN_PATH', '')
all_paths = sorted(Path('Lean').rglob('*.lean'))
violations = []
for f in all_paths:
    hits = re.findall(r'\b(?:sorry|admit|axiom|sorryAx)\b', code_only(f.read_text()))
    if hits:
        violations.append({'file': str(f), 'tokens': hits})
tracked = subprocess.check_output(['git', 'ls-files', '-z'], text=True).split('\0')
private_paths = [f for f in tracked if f and (f.lower().endswith(('.tex', '.pdf')) or f.startswith('paper/'))]
paths = all_paths
if a.current:
    paths = [f for f in paths if f.name >= 'T008' and f.name.startswith('T')]
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
rows = []
for f in paths:
    print('::group::RAW ' + str(f), flush=True)
    # Lean/ is the source root, not a module named Lean (which would shadow Lean core).
    out = build / f.relative_to('Lean').with_suffix('.olean')
    out.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(['lean', '--root=Lean', '-o', str(out), str(f)], env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    text = proc.stdout
    print(text, end='', flush=True)
    print('RAW_EXIT_CODE=' + str(proc.returncode), flush=True)
    groups = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', text, re.S)
    names = sorted({v.strip() for g in groups for v in g.split(',') if v.strip()})
    forbidden = sorted(set(names) - allowed)
    audits = len(groups) + text.count('does not depend on any axioms')
    needs_audit = bool(re.search(r'^\s*(?:theorem|lemma)\s', code_only(f.read_text()), re.M))
    ok = proc.returncode == 0 and not forbidden and 'sorryAx' not in text and (audits > 0 or not needs_audit)
    rows.append({'file': str(f), 'raw_exit_code': proc.returncode, 'axioms': names,
                 'axiom_audits': audits, 'forbidden_axioms': forbidden, 'pass': ok})
    out.with_suffix('.raw.log').write_text(text)
    print('AXIOM_GATE=' + ('PASS' if ok else 'FAIL'), flush=True)
    print('::endgroup::', flush=True)
result = {'head': os.environ.get('GITHUB_SHA', ''), 'files': rows,
          'source_violations': violations, 'private_paths': private_paths,
          'pass': bool(rows) and all(r['pass'] for r in rows) and not violations and not private_paths}
(build / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2), flush=True)
sys.exit(0 if result['pass'] else 1)
