"""Re-verify the noise-diagram relay's release-cores.json against the local release folders (read only).
Run on Windows from the repository root: python -I -B relay/reverify_release_cores.py
Writes relay/release-cores-reverify.json: for each core, the release repository's HEAD, whether its lean/
folder is clean, and whether every recorded file digest still matches.
"""
from pathlib import Path
import hashlib, json, subprocess

REPO = Path(__file__).resolve().parents[1]
REC = Path(r'\\wsl.localhost\lean-comparator\opt\uncomputable-noise-diagram-arxiv-2026-11-12\release-cores.json')
rc = json.loads(REC.read_text(encoding='utf-8'))
out = {'source': str(REC), 'source_sha256': hashlib.sha256(REC.read_bytes()).hexdigest(), 'cores': {}}
for name, r in rc.items():
    root = Path(r['release_repo'])
    head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root, capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(['git', 'status', '--porcelain', '--', 'lean'], cwd=root, capture_output=True, text=True).stdout.strip()
    bad, missing = [], []
    for rel, h in r['files'].items():
        q = root / 'lean' / rel
        if not q.is_file():
            missing.append(rel)
        elif hashlib.sha256(q.read_bytes()).hexdigest() != h:
            bad.append(rel)
    extra = [str(q.relative_to(root / 'lean')).replace('\\', '/') for q in (root / 'lean').rglob('*')
             if q.is_file() and str(q.relative_to(root / 'lean')).replace('\\', '/') not in r['files']]
    out['cores'][name] = {'release_repo': str(root), 'recorded_head': r['head'], 'head_now': head,
                          'head_unchanged': head == r['head'], 'lean_dir_clean_now': not dirty,
                          'recorded_files': len(r['files']), 'digest_mismatches': bad, 'missing': missing,
                          'unrecorded_files': extra,
                          'all_recorded_digests_match': not bad and not missing}
(REPO / 'relay' / 'release-cores-reverify.json').write_text(json.dumps(out, indent=2) + '\n', encoding='utf-8', newline='\n')
print(json.dumps({k: {a: b for a, b in v.items() if a not in ('unrecorded_files',)} for k, v in out['cores'].items()}, indent=1))
