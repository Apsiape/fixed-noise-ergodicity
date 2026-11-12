#!/usr/bin/env bash
# Install the package files ($IN/package.tar, paths relative to the workspace, written from Windows by
# relay/pack.py) into the staged release workspace and generate the module list, Challenge.lean and the
# package Audit.lean. (Adapted from the noise-diagram relay's install.sh.) Reads (never writes) the
# noise-diagram release workspace, the source of the guard helpers, the sandbox recorder and the manifest.
set -euo pipefail
D=/opt/forgetting-natural-rule-arxiv-2026-11-12-public
N=/opt/uncomputable-noise-diagram-arxiv-2026-11-12
IN=/opt/forgetting-natural-rule-lean/scratch
cd "$D"
cp "$IN/package.tar" "$D/package.tar"
tar -xf "$D/package.tar" -C "$D" --no-same-owner
cp -a "$N/project/scripts/resource_guard.py" "$D/project/scripts/resource_guard.py"
cp -a "$N/linux_guard.py" "$N/bwrap-record" "$N/release-cores.json" "$D/"
sed 's/"name": "UncomputableNoiseDiagram",/"name": "ForgettingNaturalRule",/' "$N/project/lake-manifest.json" > "$D/project/lake-manifest.json"
grep -c '"name": "ForgettingNaturalRule"' "$D/project/lake-manifest.json"
python3 -I -B - <<'PY'
from pathlib import Path
import json
P = Path('/opt/forgetting-natural-rule-arxiv-2026-11-12-public/project')
mods = ['ForgettingNaturalRule'] + sorted(
    str(p.relative_to(P).with_suffix('')).replace('/', '.') for p in (P / 'ForgettingNaturalRule').rglob('*.lean'))
(P / 'scripts/modules.json').write_text(json.dumps(mods, indent=2) + '\n')
print('modules', len(mods))
PY
python3 -I -B "$D/project/scripts/make_challenge.py" --package "$D/project"
cmp "$D/project/Challenge.lean" "$D/original/Challenge.lean" && echo "Challenge.lean identical to the source commit's"
python3 -I -B make_audit.py
ls -la "$D" "$D/project" "$D/project/scripts"
