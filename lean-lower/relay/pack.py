"""Pack the exact source commit and package overlay; python -I -B relay/pack.py COMMIT.
Adapted from the natural-rule release's relay/pack.py. Writes only the fresh
release workspace, never a precedent workspace. Archives and build outputs stay WSL.
"""
from pathlib import Path
import hashlib,io,json,subprocess,sys,tarfile,time
R=Path(__file__).resolve().parents[1]
D=Path(r'\\wsl.localhost\lean-comparator\opt\forgetting-lower-arxiv-2026-11-12')
OUT=D/'inputs'
assert not (D/'project').exists(), 'REFUSE: workspace already staged'
OUT.mkdir(parents=True,exist_ok=True)
commit=subprocess.check_output(['git','rev-parse',sys.argv[1]],cwd=R,text=True).strip()
src=subprocess.check_output(['git','archive','--format=tar',commit],cwd=R)
H=lambda b:hashlib.sha256(b).hexdigest()
PACKAGE={}
for n in ['Solution.lean','comparator.json','lakefile.lean','STATEMENT-READ.md',
          'scripts/replay.py','scripts/make_challenge.py','scripts/dump_reach.lean.txt',
          'scripts/challenge_precheck.ps1','scripts/resource_guard.py']:
    PACKAGE['project/'+n]=n
for n in ['run-linux.py','make_audit.py','make_evidence.py','host-memory-monitor.py',
          'stage.sh','install.sh','pack.py','pack_public_cores.py','linux_guard.py','bwrap-record','precheck.py']:
    PACKAGE[n]='relay/'+n
buf=io.BytesIO();files={}
with tarfile.open(fileobj=buf,mode='w',format=tarfile.PAX_FORMAT) as tf:
    for arc,rel in PACKAGE.items():
        data=(R/rel).read_bytes();assert b'\r' not in data,rel
        ti=tarfile.TarInfo(arc);ti.size=len(data);ti.mtime=int(time.time())
        ti.mode=0o755 if arc.endswith('.sh') or arc=='bwrap-record' else 0o644
        tf.addfile(ti,io.BytesIO(data));files[arc]={'from':rel,'sha256':H(data),'bytes':len(data)}
pkg=buf.getvalue()
(OUT/'source.tar').write_bytes(src);(OUT/'package.tar').write_bytes(pkg)
for n in ['stage.sh','install.sh']:(OUT/n).write_bytes((R/'relay'/n).read_bytes())
rec={'commit':commit,'source_tar_sha256':H(src),'source_tar_bytes':len(src),
     'package_tar_sha256':H(pkg),'package_files':files,'utc_epoch':time.time()}
(OUT/'pack-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
(R/'relay/pack-receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print('packed',commit,len(src),len(pkg),flush=True)
