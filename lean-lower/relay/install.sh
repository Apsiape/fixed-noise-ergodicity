#!/usr/bin/env bash
# Adapted from the natural-rule release install.sh.
set -euo pipefail
D=/opt/forgetting-lower-arxiv-2026-11-12
N=/opt/forgetting-natural-rule-arxiv-2026-11-12-public
cp "$D/inputs/package.tar" "$D/package.tar"
tar -xf "$D/package.tar" -C "$D" --no-same-owner
sed 's/"name": "ForgettingNaturalRule",/"name": "ForgettingLower",/' "$N/project/lake-manifest.json" > "$D/project/lake-manifest.json"
chmod +x "$D/bwrap-record"
python3 -I -B - <<'PY'
from pathlib import Path
import json
P=Path('/opt/forgetting-lower-arxiv-2026-11-12/project')
mods=['ForgettingLower']+sorted(p.relative_to(P).with_suffix('').as_posix().replace('/','.') for p in (P/'ForgettingLower').rglob('*.lean'))
(P/'scripts/modules.json').write_text(json.dumps(mods,indent=2)+'\n')
print('development modules',len(mods),flush=True)
PY
cd "$D"
python3 -I -B project/scripts/make_challenge.py --package project
python3 -I -B make_audit.py
echo INSTALLED
