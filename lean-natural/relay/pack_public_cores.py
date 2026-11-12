"""Hand the PUBLIC Lean trees of the reused cores to WSL (session 3b; QB decision 2 of 12 Nov 2026: a reader can
reproduce only from public sources, so the package vendors the published lean/ folders).
Run on Windows from the repository root: python -I -B relay/pack_public_cores.py

For each reused core that has a public Lean release, reads its release repository READ ONLY (git rev-parse,
ls-tree and cat-file of the release commit, which take no lock; reading working-tree files and SHA256SUMS) and
writes into this core's own development folder /opt/forgetting-natural-rule-lean/scratch (through
\\\\wsl.localhost; never into a precedent workspace or a release folder):
  * public-<Core>.tar - the lean/ folder of the release commit, paths relative to lean/, with the bytes of the git
    blobs (the release repositories set `* -text`, so the blobs are the published bytes) and their git file modes;
  * public-cores-receipt.json - per core: the release repository, commit, its lean/ tree hash, origin/main, the
    version tag (if any), CITATION.cff version and DOI, every file's sha256, and three cross-checks: the working
    tree, the release's SHA256SUMS, and release-cores.json (recorded by the noise-diagram relay).
The receipt is also written to relay/public-cores-receipt.json.

The noise-diagram core has no public Lean release (its public release v1.1.0, commit a0b903e of
uncomputable-noise-diagram-release, has no lean/ folder); it stays vendored from its release package workspace.
"""
from pathlib import Path
import hashlib, io, json, re, subprocess, tarfile

REPO = Path(__file__).resolve().parents[1]
OUT = Path(r'\\wsl.localhost\lean-comparator\opt\forgetting-natural-rule-lean\scratch')
RC = Path(r'\\wsl.localhost\lean-comparator\opt\uncomputable-noise-diagram-arxiv-2026-11-12\release-cores.json')
CORES = {
    'FixedNoiseErgodicity': {
        'release_repo': r'C:\Infanox\fixed-noise-ergodicity-release',
        'commit': 'bdfca9b804e9dbd95dc2e1940d8b9974fe77bed2',      # "Record the version 1.4.0 DOI" (origin/main)
        'version_commit': 'eda83c15235f9434fa98bcd58b27705648e2e12f',  # "Version 1.4.0" (same lean/ tree)
        'tag': 'v1.4.0', 'version': '1.4.0', 'doi': '10.5281/zenodo.24126025',
        'paper': 'Forgetting under noise is undecidable',
        'public_url': 'https://github.com/Apsiape/fixed-noise-ergodicity/tree/v1.4.0/lean'},
    'UndecidablePhaseDiagram': {
        'release_repo': r'C:\Infanox\undecidable-phase-diagram-release',
        'commit': 'd57af60115fd028058340296458e4de001f491b4',      # "Record the version 1.2.0 DOI" (origin/main)
        'version_commit': '007fbc270ce5769847d70e25733f608e3a82822a',  # tag v1.2.0 (same lean/ tree)
        'tag': 'v1.2.0', 'version': '1.2.0', 'doi': '10.5281/zenodo.24144192',
        'paper': 'An uncomputable phase diagram at positive temperature for one classical lattice model',
        'public_url': 'https://github.com/Apsiape/undecidable-phase-diagram/tree/v1.2.0/lean'},
}
H = lambda b: hashlib.sha256(b).hexdigest()


def git(root, *args, text=True):
    r = subprocess.run(['git', '--no-optional-locks', *args], cwd=root, capture_output=True, check=True)
    return r.stdout.decode('utf-8').strip() if text else r.stdout


rc = json.loads(RC.read_text(encoding='utf-8'))
receipt = {'release_cores_json': str(RC), 'release_cores_json_sha256': H(RC.read_bytes()), 'cores': {}}
OUT.mkdir(exist_ok=True)
for name, c in CORES.items():
    root = Path(c['release_repo'])
    tree = git(root, 'rev-parse', c['commit'] + ':lean')
    vtree = git(root, 'rev-parse', c['version_commit'] + ':lean')
    origin = git(root, 'rev-parse', 'refs/remotes/origin/main')
    tag = subprocess.run(['git', '--no-optional-locks', 'rev-parse', '-q', '--verify', 'refs/tags/' + c['tag'] + '^{commit}'],
                         cwd=root, capture_output=True, text=True).stdout.strip() or None
    cit = git(root, 'show', c['commit'] + ':CITATION.cff')
    cit_version = re.search(r'^version:\s*(\S+)', cit, re.M).group(1)
    cit_doi = re.search(r'^doi:\s*"?([^"\s]+)', cit, re.M).group(1)
    sums = {}
    for line in git(root, 'show', c['commit'] + ':SHA256SUMS').splitlines():
        h, p = line.split(None, 1)
        if p.startswith('lean/'):
            sums[p[5:]] = h
    entries = []
    for rec in git(root, 'ls-tree', '-r', '-z', c['commit'], '--', 'lean/', text=False).split(b'\0'):
        if not rec:
            continue
        meta, path = rec.split(b'\t', 1)
        mode, typ, oid = meta.decode().split()
        assert typ == 'blob', (name, path)
        entries.append((path.decode('utf-8')[5:], mode, oid))
    buf = io.BytesIO()
    epoch = int(git(root, 'show', '-s', '--format=%ct', c['commit']))
    files, wt_diff, sums_diff, rc_diff = {}, [], [], []
    rcf = rc.get(name, {}).get('files', {})
    with tarfile.open(fileobj=buf, mode='w', format=tarfile.PAX_FORMAT) as tf:
        for rel, mode, oid in sorted(entries):
            data = git(root, 'cat-file', 'blob', oid, text=False)
            h = H(data)
            files[rel] = {'sha256': h, 'bytes': len(data), 'mode': mode, 'git_blob': oid}
            wt = root / 'lean' / rel
            if not wt.is_file() or H(wt.read_bytes()) != h:
                wt_diff.append(rel)
            if sums.get(rel) != h:
                sums_diff.append(rel)
            if rcf and rcf.get(rel) != h:
                rc_diff.append(rel)
            ti = tarfile.TarInfo(rel)
            ti.size, ti.mtime = len(data), epoch
            ti.mode = 0o755 if mode == '100755' else 0o644
            tf.addfile(ti, io.BytesIO(data))
    data = buf.getvalue()
    (OUT / f'public-{name}.tar').write_bytes(data)
    receipt['cores'][name] = {
        **c, 'lean_tree': tree, 'lean_tree_at_version_commit': vtree, 'lean_tree_same_at_version_commit': tree == vtree,
        'origin_main': origin, 'commit_is_origin_main': origin == c['commit'],
        'local_tag_commit': tag, 'local_tag_present': tag is not None,
        'citation_version': cit_version, 'citation_doi': cit_doi,
        'citation_matches': cit_version == c['version'] and cit_doi == c['doi'],
        'tar': f'public-{name}.tar', 'tar_sha256': H(data), 'tar_bytes': len(data), 'tar_mtime': epoch,
        'file_count': len(files),
        'working_tree_mismatches': wt_diff, 'sha256sums_count': len(sums), 'sha256sums_mismatches': sums_diff,
        'sha256sums_extra': sorted(set(sums) - set(files)),
        'release_cores_json_count': len(rcf), 'release_cores_json_mismatches': rc_diff,
        'release_cores_json_extra': sorted(set(rcf) - set(files)),
        'files': files}
    print(name, json.dumps({k: v for k, v in receipt['cores'][name].items() if k != 'files'}, indent=1))
txt = json.dumps(receipt, indent=2) + '\n'
(OUT / 'public-cores-receipt.json').write_text(txt, encoding='utf-8', newline='\n')
(REPO / 'relay' / 'public-cores-receipt.json').write_text(txt, encoding='utf-8', newline='\n')
