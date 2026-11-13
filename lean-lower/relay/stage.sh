#!/usr/bin/env bash
# Adapted from the natural-rule release stage.sh; no precedent workspace is written.
set -euo pipefail
D=/opt/forgetting-lower-arxiv-2026-11-12
F=/opt/forgetting-arxiv-2026-11-10
IN="$D/inputs"
test ! -e "$D/project" || { echo 'REFUSE: project exists'; exit 1; }
mkdir -p "$D/original" "$D/project/vendor" "$D/environment" "$D/results" "$D/kernels" "$D/evidence" "$D/attempts"
cp "$IN/source.tar" "$D/source.tar"
cp "$IN/pack-receipt.json" "$D/pack-receipt.json"
tar -xf "$D/source.tar" -C "$D/original"
tar -xf "$D/source.tar" -C "$D/project"
cp -a "$F/toolchain" "$D/toolchain"
cp -a "$F/bubblewrap" "$D/bubblewrap"
for p in plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli mathlib; do
  cp -a "$F/project/vendor/$p" "$D/project/vendor/$p"
done
cp "$IN/public-cores-receipt.json" "$D/public-cores-receipt.json"
for name in FixedNoiseErgodicity UndecidablePhaseDiagram UncomputableNoiseDiagram ForgettingNaturalRule; do
  cp "$IN/public-$name.tar" "$D/public-$name.tar"
  mkdir -p "$D/project/vendor/$name"
  tar -xf "$D/public-$name.tar" -C "$D/project/vendor/$name" --no-same-owner
done
python3 -I -B - <<'PY'
from pathlib import Path
import hashlib,json
D=Path('/opt/forgetting-lower-arxiv-2026-11-12')
rc=json.loads((D/'public-cores-receipt.json').read_text())
for name,c in rc['cores'].items():
    V=D/'project/vendor'/name
    have={q.relative_to(V).as_posix():hashlib.sha256(q.read_bytes()).hexdigest() for q in V.rglob('*') if q.is_file()}
    want={k:v['sha256'] for k,v in c['files'].items()}
    assert have==want,name
    print(name,'byte-identical public folder',len(have),'files',flush=True)
PY
echo "hard links in vendor: $(find "$D/project/vendor" -links +1 -type f | wc -l)"
sync
echo 1 > /proc/sys/vm/drop_caches
grep MemAvailable /proc/meminfo
echo STAGED
