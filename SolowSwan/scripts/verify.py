"""Build and freshly re-elaborate every proof, rejecting extra axioms and placeholders."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re, shutil, subprocess

ROOT = Path(__file__).resolve().parents[1]
CONFIG = json.loads((ROOT / 'proof-manifest.json').read_text())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lake', default=shutil.which('lake') or 'lake')
args = parser.parse_args()
out = ROOT / 'verification'
out.mkdir(exist_ok=True)

def run(command, logname):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding='utf-8', errors='replace', timeout=1200)
    log = result.stdout + result.stderr
    (out / logname).write_text(log, encoding='utf-8', newline='\n')
    assert result.returncode == 0, log
    assert not any(x in log for x in ('error:', 'error(', 'PANIC', 'sorryAx', 'warning:')), log
    return log

imports, bodies, names, counts, hashes = [], [], [], {}, {}
for path in CONFIG['modules']:
    raw = (ROOT / path).read_bytes()
    hashes[path] = hashlib.sha256(raw).hexdigest()
    namespace, body, count = [], [], 0
    for line in raw.decode('utf-8').splitlines():
        if line.startswith('import '):
            if not line.startswith('import ' + CONFIG['library'] + '.') and line not in imports:
                imports.append(line)
            continue
        body.append(line)
        if line.startswith('namespace '):
            namespace.append(line[len('namespace '):].strip())
        elif line.startswith('end '):
            namespace.pop()
        elif match := re.match(r'(?:@\[simp\] )?theorem ([\w.]+)', line):
            names.append('.'.join(namespace + [match[1]]))
            count += 1
    assert not namespace
    counts[path] = count
    bodies.append('\n'.join(body))
assert counts == CONFIG['theorem_counts'], counts
fresh = '\n'.join(imports) + '\n\n' + '\n\n'.join(bodies)
fresh += '\n\n' + '\n'.join('#print axioms ' + n for n in names) + '\n'
freshpath = out / 'FreshAudit.lean'
freshpath.write_text(fresh, encoding='utf-8', newline='\n')
run([args.lake, 'build'], 'build.txt')
log = run([args.lake, 'env', 'lean', str(freshpath)], 'fresh-audit.txt')
axioms = {}
for name in names:
    match = re.search(re.escape("'" + name + "'") + r' depends on axioms:\s*\[([^]]*)\]', log)
    if match:
        found = [a.strip() for a in match[1].split(',') if a.strip()]
    else:
        assert "'" + name + "' does not depend on any axioms" in log, name
        found = []
    assert set(found) <= ALLOWED, (name, found)
    axioms[name] = found
for path in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'proof-manifest.json', 'scripts/verify.py', 'UNLICENSE']:
    hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
record = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'theorems': len(names),
          'module_theorems': counts, 'full_build': 'passed', 'fresh_source_compilation': 'passed',
          'axioms': axioms, 'source_sha256': hashes,
          'fresh_audit_sha256': hashlib.sha256(freshpath.read_bytes()).hexdigest(),
          'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
          'scope': CONFIG['scope'], 'source_provenance': CONFIG['source_commit']}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8', newline='\n')
print(f"Passed full build, fresh source compilation, and {len(names)} theorem axiom audits.")
