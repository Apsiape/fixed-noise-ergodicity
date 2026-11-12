"""Hand the release inputs to WSL (run on Windows from the repository root: python -I -B relay/pack.py COMMIT).

Writes into this core's own development folder /opt/forgetting-natural-rule-lean/scratch (through
\\\\wsl.localhost; /mnt/c is not mounted in the distro), never into a precedent workspace:
  * source.tar  - `git archive --format=tar COMMIT` (the frozen source commit; no build outputs);
  * package.tar - the package files from the working tree, with paths relative to the release workspace
                  (project/... and the relay scripts at the workspace root);
  * stage.sh, install.sh - the two staging scripts, run with `wsl.exe -d lean-comparator -- bash <path>`;
  * pack-receipt.json - the sha256 of each of them and of every packed file.
"""
from pathlib import Path
import hashlib, io, json, subprocess, sys, tarfile, time

REPO = Path(__file__).resolve().parents[1]
OUT = Path(r'\\wsl.localhost\lean-comparator\opt\forgetting-natural-rule-lean\scratch')
commit = sys.argv[1]
H = lambda b: hashlib.sha256(b).hexdigest()

src = subprocess.run(['git', 'archive', '--format=tar', commit], cwd=REPO, capture_output=True, check=True).stdout
full = subprocess.run(['git', 'rev-parse', commit], cwd=REPO, capture_output=True, check=True, text=True).stdout.strip()

PACKAGE = {  # workspace path -> repository path
    'project/Solution.lean': 'Solution.lean',
    'project/comparator.json': 'comparator.json',
    'project/lakefile.lean': 'lakefile.lean',
    'project/scripts/replay.py': 'scripts/replay.py',
    'run-linux.py': 'relay/run-linux.py',
    'make_audit.py': 'relay/make_audit.py',
    'make_evidence.py': 'relay/make_evidence.py',
    'host-memory-monitor.py': 'relay/host-memory-monitor.py',
    'stage.sh': 'relay/stage.sh',
    'install.sh': 'relay/install.sh',
    'pack.py': 'relay/pack.py',
    'pack_public_cores.py': 'relay/pack_public_cores.py',
}
buf = io.BytesIO()
now = int(time.time())
files = {}
with tarfile.open(fileobj=buf, mode='w', format=tarfile.PAX_FORMAT) as tf:
    for arc, rel in PACKAGE.items():
        data = (REPO / rel).read_bytes()
        assert b'\r' not in data, rel
        ti = tarfile.TarInfo(arc)
        ti.size, ti.mtime, ti.mode = len(data), now, 0o755 if arc.endswith('.sh') else 0o644
        tf.addfile(ti, io.BytesIO(data))
        files[arc] = {'from': rel, 'sha256': H(data), 'bytes': len(data)}
pkg = buf.getvalue()

OUT.mkdir(exist_ok=True)
(OUT / 'source.tar').write_bytes(src)
(OUT / 'package.tar').write_bytes(pkg)
for name in ('stage.sh', 'install.sh'):
    (OUT / name).write_bytes((REPO / 'relay' / name).read_bytes())
rec = {'commit': full, 'source_tar_sha256': H(src), 'source_tar_bytes': len(src),
       'package_tar_sha256': H(pkg), 'package_files': files, 'utc_epoch': time.time()}
(OUT / 'pack-receipt.json').write_text(json.dumps(rec, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({k: v for k, v in rec.items() if k != 'package_files'}, indent=1))
