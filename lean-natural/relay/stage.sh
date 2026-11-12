#!/usr/bin/env bash
# Stage the release workspace /opt/forgetting-natural-rule-arxiv-2026-11-12-public (session 3b; session 3 staged
# /opt/forgetting-natural-rule-arxiv-2026-11-12, kept unchanged beside it as its record).
# (Adapted from the noise-diagram relay's stage.sh.) Reads (never writes) the precedent release workspaces.
# Inputs in $IN (this core's own development folder, not a precedent), written there from Windows:
#   source.tar - the git archive of the frozen source commit (relay/pack.py);
#   public-FixedNoiseErgodicity.tar, public-UndecidablePhaseDiagram.tar, public-cores-receipt.json - the lean/
#   folders of the PUBLIC releases of the forgetting core (v1.4.0, DOI 10.5281/zenodo.24126025) and of the
#   hard-model core (v1.2.0, DOI 10.5281/zenodo.24144192), with the bytes of the git blobs of the release
#   commits (relay/pack_public_cores.py). QB decision 2 (12 Nov 2026): a reader can reproduce only from public
#   sources, so the package vendors the published trees.
# The noise-diagram core has no public Lean release; it is vendored, as in session 3, from its release package
# workspace /opt/uncomputable-noise-diagram-arxiv-2026-11-12/project (git archive ec67163 + package files).
set -euo pipefail
D=/opt/forgetting-natural-rule-arxiv-2026-11-12-public
F=/opt/forgetting-arxiv-2026-11-10
N=/opt/uncomputable-noise-diagram-arxiv-2026-11-12
IN=/opt/forgetting-natural-rule-lean/scratch
test ! -e "$D" || { echo "REFUSE: $D exists"; exit 1; }
mkdir -p "$D/original" "$D/project/vendor" "$D/environment" "$D/results" "$D/kernels" "$D/evidence" "$D/attempts"
cp "$IN/source.tar" "$D/source.tar"
tar -xf "$D/source.tar" -C "$D/original"
tar -xf "$D/source.tar" -C "$D/project"
echo "sources extracted"
cp -a "$F/toolchain" "$D/toolchain"
cp -a "$F/bubblewrap" "$D/bubblewrap"
echo "toolchain, bubblewrap copied"
for p in plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli mathlib; do
  cp -a "$F/project/vendor/$p" "$D/project/vendor/$p"
done
echo "pinned dependency tree copied"
# The forgetting and hard-model cores: the public lean/ folders, extracted whole (the forgetting core must be
# whole: ForgettingNaturalRule.Reduction imports FixedNoiseErgodicity.Undecidable).
cp "$IN/public-cores-receipt.json" "$D/public-cores-receipt.json"
for name in FixedNoiseErgodicity UndecidablePhaseDiagram; do
  cp "$IN/public-$name.tar" "$D/public-$name.tar"
  mkdir -p "$D/project/vendor/$name"
  tar -xf "$D/public-$name.tar" -C "$D/project/vendor/$name" --no-same-owner
done
# The noise-diagram core: rsync -a (cp -a semantics) of its release package workspace, without its own vendor/
# (the same pinned tree, supplied once above), build outputs (.lake/) and its relay's heartbeat files.
rsync -a --exclude=/vendor --exclude=/.lake --exclude=/.host-memory.json --exclude=/.host-memory.stop \
  "$N/project/" "$D/project/vendor/UncomputableNoiseDiagram/"
echo "cores vendored"
python3 -I -B - <<'PY'
from pathlib import Path
import hashlib, json
D = Path('/opt/forgetting-natural-rule-arxiv-2026-11-12-public')
rc = json.loads((D / 'public-cores-receipt.json').read_text())
for name, c in rc['cores'].items():
    V = D / 'project/vendor' / name
    assert hashlib.sha256((D / c['tar']).read_bytes()).hexdigest() == c['tar_sha256'], name
    have = {q.relative_to(V).as_posix(): hashlib.sha256(q.read_bytes()).hexdigest() for q in V.rglob('*') if q.is_file()}
    want = {k: v['sha256'] for k, v in c['files'].items()}
    assert have == want, (name, sorted(set(have) ^ set(want)), [k for k in want if have.get(k) != want[k]])
    print(name, 'vendored tree byte-identical to the public release', c['version'], c['doi'], len(have), 'files')
PY
echo "hard links in vendor: $(find "$D/project/vendor" -links +1 -type f | wc -l)"
du -sh "$D/toolchain" "$D/project/vendor" "$D/project/vendor/FixedNoiseErgodicity" \
  "$D/project/vendor/UndecidablePhaseDiagram" "$D/project/vendor/UncomputableNoiseDiagram"
sync
echo 1 > /proc/sys/vm/drop_caches
grep MemAvailable /proc/meminfo
echo STAGED
