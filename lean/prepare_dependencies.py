"""Copy the pinned dependency sources into vendor/, checking every file against
pins/DEPENDENCY-SOURCES.json. Runs no Git command and copies no build objects."""
from pathlib import Path
import argparse,hashlib,json,shutil
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--source-dir',required=True,type=Path,help='directory with one checkout per package of pins/DEPENDENCIES.json, each named by the package name')
ap.add_argument('--check-only',action='store_true',help='verify the sources without copying them')
a=ap.parse_args()
source=a.source_dir.resolve();target=ROOT/'vendor';assert source!=target.resolve(),'Choose a source directory other than vendor/'
entries=json.loads((ROOT/'pins/DEPENDENCY-SOURCES.json').read_text(encoding='utf-8'))['files']
# One Mathlib cache-tool file, outside the import closure of the proofs, is replaced so that
# `lake exe cache get` works with path dependencies; pins/DEPENDENCY-SOURCES.json records the replacement.
overrides={'mathlib/Cache/Requests.lean': ROOT/'cache-tool/Requests.lean'}
for entry in entries:
 rel=Path(entry['path']);assert not rel.is_absolute() and '..' not in rel.parts
 p=overrides.get(entry['path'],source/rel);assert p.is_file(),'Missing dependency source: '+str(rel)
 with p.open('rb') as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
 assert digest==entry['sha256'],'Wrong dependency source: '+str(rel)
if a.check_only:
 print('Verified',len(entries),'exact dependency sources, including the one bundled cache-tool replacement.');raise SystemExit(0)
for entry in entries:
 rel=Path(entry['path']);q=target/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(overrides.get(entry['path'],source/rel),q)
print('Verified and copied',len(entries),'source files into vendor/. Next, from this directory: lake exe cache get; lake build')
