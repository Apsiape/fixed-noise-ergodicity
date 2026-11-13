"""Compare reachable statement constants, using the precedent dump and replay guards."""
from pathlib import Path
import hashlib, json, subprocess
D = Path(__file__).resolve().parent
P = D / 'project'
S = P / 'scratch'
S.mkdir(exist_ok=True)
cmd = (P/'scripts/dump_reach.lean.txt').read_text()
(S/'DevDump.lean').write_text('import ForgettingLower\n\nset_option autoImplicit false\n' + cmd)
(S/'ChDump.lean').write_text((P/'Challenge.lean').read_text() + '\n' + cmd)
subprocess.run(['python3','-I','-B','scripts/replay.py','--resume','scratch.DevDump','scratch.ChDump'], cwd=P, check=True)
def get(name):
    p = P / '.lake/replay' / (name+'.log')
    t = p.read_text()
    i,j = t.index('DUMP-BEGIN'),t.index('DUMP-END')
    return {l.strip() for l in t[i:j].split('\n')[1:] if l.strip()}
a,b = get('scratch.DevDump'),get('scratch.ChDump')
rec = {'status':'PASS' if a == b else 'FAIL','development_constants':len(a),
       'challenge_constants':len(b),'only_development':sorted(a-b),'only_challenge':sorted(b-a),
       'method':'name, declaration kind, expression hash of type and definition value; roots type only',
       'prefixes':['FNE','UPD','UND','FNR','FLD'],
       'development':sorted(a),'challenge':sorted(b)}
(D/'evidence/CHALLENGE-PRECHECK.json').write_text(json.dumps(rec,indent=2)+'\n')
print(rec['status'],len(a),len(b),flush=True)
assert a == b, (sorted(a-b),sorted(b-a))
