"""Collect Z4 release receipts. Adapted from the natural-rule release evidence script.
Run in WSL with python3 -I -B; only this release workspace is written.
"""
from pathlib import Path
import hashlib, importlib.util, json, re, shutil, subprocess

D=Path(__file__).resolve().parent
P,O,E,R,K=[D/n for n in ['project','original','evidence','results','kernels']]
E.mkdir(exist_ok=True)
CORES=['FixedNoiseErgodicity','UndecidablePhaseDiagram','UncomputableNoiseDiagram','ForgettingNaturalRule']
DEPS=['plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli','mathlib']
FINAL={'FLD.z4_classification':'FLD.Z4Classification',
       'FLD.z4_machine_corollary':'FLD.Z4MachineCorollary',
       'FLD.z4_raw_undecidable':'FLD.Z4RawUndecidable'}
FROZEN='58cb7388400f05f2986d2b2cc9154a99a554eed4b384f10c8809b706d3b244c4'
STD={'propext','Classical.choice','Quot.sound'}
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(p.read_text())
def dump(n,obj):(E/n).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n')
spec=importlib.util.spec_from_file_location('census',P/'scripts/sorry_census.py')
census=importlib.util.module_from_spec(spec);spec.loader.exec_module(census)

hist=[json.loads(l) for l in (P/'.lake/replay/history.ndjson').read_text().splitlines() if l.strip()]
end=next(i for i,r in enumerate(hist) if r['module']=='Audit' and r['exit']==0)
fresh=hist[:end+1]
mods=read(P/'scripts/modules.json')
coremods={c:[r['module'] for r in fresh if r['module'].split('.')[0]==c] for c in CORES}
build={'status':'PASS' if all(r['exit']==0 for r in fresh) and len(fresh)==len({r['module'] for r in fresh}) else 'FAIL',
       'lean_version':read(P/'.lake/replay/latest.json')['lean'],
       'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679',
       'source_commit':read(D/'pack-receipt.json')['commit'],
       'project_modules':len(mods),'package_modules':3,'core_modules_compiled_by_core':{k:len(v) for k,v in coremods.items()},
       'core_modules_compiled':sum(map(len,coremods.values())),'total_modules':len(fresh),
       'fresh_no_resume':True,'lean_threads':1,'lean_heap_MiB':5000,'memory_floor_bytes':8*1024**3,
       'linux_process_tree_stop_rss_bytes':9000000000,
       'peak_observed_tree_rss_bytes':max(r['peak_tree_bytes'] for r in fresh),
       'minimum_available_before_build_bytes':min(r['free_before_bytes'] for r in fresh),
       'fresh_full_replay_seconds_total':round(sum(r['seconds'] for r in fresh),3),
       'fresh_full_replay_warnings_total':sum(r['warnings'] for r in fresh),
       'records':fresh,'later_records':hist[end+1:],
       'dependency_policy':'Four public cores compiled from sources; no core or development objects reused. Nine pinned dependencies use prebuilt objects.'}
assert len(fresh)==len(mods)+3+sum(map(len,coremods.values()))
cache=read(P/'.lake/replay/completed.json')
source_checks={}
for rec in fresh:
    n=rec['module'];rel=n.replace('.','/')+'.lean'
    root=P/'vendor'/n.split('.')[0] if rec['kind']=='core' else P
    source_checks[n]={'compiled_sha256':cache[n]['source'],'final_sha256':sha(root/rel)}
assert all(v['compiled_sha256']==v['final_sha256'] for v in source_checks.values())
build['compiled_source_hashes']=source_checks
dump('BUILD.json',build)

cr=read(R/'comparator-receipt.json')
inv=[json.loads(l) for l in (D/'bwrap-invocations.ndjson').read_text().splitlines() if l.strip()]
log=(R/'comparator.log').read_text()
imports=re.findall(r'^import\s+(\S+)',census.strip((P/'Challenge.lean').read_text()),re.M)
cr.update({'theorem_names':list(FINAL),'permitted_axioms':sorted(STD),
           'sandbox_invocations':len(inv),'sandbox_observed':bool(inv) and all('--unshare-all' in x['arguments'] for x in inv),
           'sandbox_invocation_commands':[x['arguments'][x['arguments'].index('--')+1:] for x in inv],
           'default_kernel_accepts':'Lean default kernel accepts the solution' in log,
           'verdict':'Your solution is okay!' if 'Your solution is okay!' in log else None,
           'challenge_imports':imports,'challenge_imports_only_mathlib':bool(imports) and all(i.startswith('Mathlib.') for i in imports),
           'challenge_sha256':sha(P/'Challenge.lean'),'solution_sha256':sha(P/'Solution.lean')})
cr['status']='PASS' if cr['exit']==0 and cr['sandbox_observed'] and cr['default_kernel_accepts'] and cr['verdict'] and cr['challenge_imports_only_mathlib'] else 'FAIL'
dump('COMPARATOR.json',cr)

xr=read(R/'export-receipt.json')
kr={'export':xr,'kernel_replays':{k:read(K/(k+'-receipt.json')) for k in ['leanchecker','nanoda','nanoda-negative-control']}}
kv=kr['kernel_replays']
negative=kv['nanoda-negative-control']
kr['status']='PASS' if xr['exit']==0 and kv['leanchecker']['exit']==0 and kv['nanoda']['exit']==0 and negative['exit']!=0 and 'unpermitted axiom' in negative['log_tail'] and 'Classical.choice' in negative['log_tail'] else 'FAIL'
assert sha(R/'Solution.ndjson')==xr['sha256']
dump('KERNEL-REPLAY.json',kr)

ax=(P/'AXIOMS.txt').read_text()
shutil.copy2(P/'AXIOMS.txt',E/'AXIOMS.txt')
shutil.copy2(P/'.lake/replay/ForgettingLower.Audit.log',E/'AXIOMS-DEV-AUDIT.txt')
def decls(tag):
    out=[]
    for l in ax.splitlines():
        if l.startswith(tag+':'):
            x=json.loads(l.split(':',1)[1]);out.append([x[0],x[1][0],x[1][1]])
    return out
own,cores=decls('FLD_DECL'),decls('CORE_DECL')
printed=dict(re.findall(r"^'?([^'\s]+)'? depends on axioms: \[([^\]]*)\]",ax,re.M))
fa={n:[a.strip() for a in printed.get(n,'').split(',') if a.strip()] for n in FINAL}
bad=[d for d in own+cores if not set(d[2])<=STD]
roots=re.findall(r'^#print axioms (\S+)$',(P/'Audit.lean').read_text(),re.M)
audit={'status':'PASS' if not bad and 'FLD_FINAL_TYPES_OK' in ax and all(set(v)==STD for v in fa.values()) else 'FAIL',
       'final_theorem_types':FINAL,'final_theorem_axioms':fa,'permitted_axioms':sorted(STD),
       'explicit_roots':len(roots),'development_declarations_count':len(own),'imported_core_declarations_count':len(cores),
       'imported_core_declarations_by_core':{c:sum(d[1].startswith(c) for d in cores) for c in CORES},
       'including_generated_and_private':True,'unexpected':bad,'declarations':own,'core_declarations':cores,
       'axioms_text_sha256':sha(E/'AXIOMS.txt')}
assert int(re.search(r'FLD_DECL_COUNT:(\d+)',ax).group(1))==len(own)
assert int(re.search(r'CORE_DECL_COUNT:(\d+)',ax).group(1))==len(cores)
dump('AXIOM-AUDIT.json',audit)

leanfiles=[P/'ForgettingLower.lean',*sorted((P/'ForgettingLower').rglob('*.lean')),P/'Challenge.lean',P/'Solution.lean',P/'Audit.lean']
forb=re.compile(r'\b(native_decide|implemented_by|admit)\b|@\[extern|^\s*axiom\s|autoImplicit\s+true',re.M)
hits=[];sorries=[];noimp=[]
for p in leanfiles:
    code=census.strip(p.read_text());rel=p.relative_to(P).as_posix()
    hits += [{'file':rel,'line':code[:m.start()].count('\n')+1,'token':m.group()} for m in forb.finditer(code)]
    sorries += [{'file':rel,'line':code[:m.start()].count('\n')+1} for m in re.finditer(r'(?<![\w.])sorry(?![\w])',code)]
    if 'set_option autoImplicit false' not in code:noimp.append(rel)
lint=subprocess.run(['bash','scripts/lint.sh'],cwd=P,capture_output=True,text=True)
source={'status':'PASS' if not hits and not noimp and len(sorries)==3 and all(s['file']=='Challenge.lean' for s in sorries) and lint.returncode==0 else 'FAIL',
        'development_files':len(mods),'lean_files_checked':[p.relative_to(P).as_posix() for p in leanfiles],
        'forbidden_constructs':hits,'sorry_tokens':sorries,'files_without_autoImplicit_false':noimp,
        'lint_exit':lint.returncode,'lint_output':lint.stdout,'development_sorry_count':sum(s['file']!='Challenge.lean' for s in sorries)}
dump('SOURCE-AUDIT.json',source)

orig={p.relative_to(O).as_posix():sha(p) for p in O.rglob('*') if p.is_file()}
changed=[n for n,h in orig.items() if not (P/n).is_file() or sha(P/n)!=h]
proof_changes=[n for n in changed if n.endswith('.lean')]
original={'status':'PASS' if not proof_changes and sha(P/'ForgettingLower/Statements.lean')==FROZEN else 'FAIL',
          'commit':read(D/'pack-receipt.json')['commit'],'archive_sha256':sha(D/'source.tar'),
          'frozen_statement_sha256':sha(P/'ForgettingLower/Statements.lean'),'frozen_statement_expected':FROZEN,
          'original_lean_sources_unchanged':not proof_changes,'changed_original_files':changed,
          'note':'AXIOMS.txt is the fresh package audit. Release documentation may replace development status; no original Lean source is changed.',
          'files':orig}
dump('ORIGINAL-SOURCE.json',original)
choices=[{'file':p.relative_to(O).as_posix(),'line':i,'text':l.strip()} for p in [O/'ForgettingLower/Statements.lean'] for i,l in enumerate(p.read_text().splitlines(),1) if '[choice]' in l]
dump('CHOICES.json',{'count':len(choices),'choices':choices,'note':'All choices precede the freeze. No new mathematical choices in packaging.'})

public=read(D/'public-cores-receipt.json')['cores'];vc={}
for c,rec in public.items():
    V=P/'vendor'/c
    have={q.relative_to(V).as_posix():sha(q) for q in V.rglob('*') if q.is_file()}
    want={n:f['sha256'] for n,f in rec['files'].items()}
    comparisons={n:{'vendored_sha256':have.get(n),'public_sha256':want.get(n),'identical':have.get(n)==want.get(n)} for n in sorted(set(have)|set(want))}
    vc[c]={'status':'PASS' if have==want else 'FAIL','files':len(have),'public_release_files':len(want),
           'byte_identical_to_public_release_tree':have==want,'version':rec['version'],'doi':rec['doi'],
           'release_commit':rec['commit'],'release_folder':rec['folder'],'public_url':rec['public_url'],
           'public_tree':rec['tree'],'tree_equals_tag':rec['tree_equals_tag'],
           'citation_doi':rec['citation_doi'],'citation_doi_matches_requested':rec['citation_doi_matches_requested'],
           'compiled_modules':coremods[c],'file_comparisons':comparisons}
dump('VENDOR-CORES.json',vc)

ref=P/'vendor/FixedNoiseErgodicity/pins/DEPENDENCY-SOURCES.json'
manifest=read(ref);listed={f['path']:f for f in manifest['files']};mism=[]
for n,f in listed.items():
    q=P/'vendor'/n
    if not q.is_file() or q.stat().st_size!=f['bytes'] or sha(q)!=f['sha256']:mism.append(n)
unlisted=[q.relative_to(P/'vendor').as_posix() for d in DEPS for q in (P/'vendor'/d).rglob('*.lean') if '.lake' not in q.parts and q.relative_to(P/'vendor').as_posix() not in listed]
dump('DEPENDENCY-CHECK.json',{'status':'PASS' if not mism and not unlisted else 'FAIL',
     'reference':'vendor/FixedNoiseErgodicity/pins/DEPENDENCY-SOURCES.json','reference_sha256':sha(ref),
     'mathlib_commit':'56a005855ea17e0b0958f73ec801ae140b0a1679',
     'checked_dependency_source_files':len(listed),'mismatches':mism,'unlisted_lean_sources':unlisted,
     'note':'Sources checked file by file; prebuilt dependency objects used. Standalone kernels check the exported proof closure.'})
bins=[D/'toolchain/bin'/n for n in ['lean','lake','leanexport','leanchecker','nanoda_bin']]+[D/'bubblewrap/usr/bin/bwrap']
dump('BINARY-DIGESTS.json',{'records':[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in bins],
      'toolchain':'cp -a of /opt/forgetting-arxiv-2026-11-10/toolchain; Lean 4.35.0 eb6cafb7290e8bd5f2937522d8d804f58f02bafc'})
checks={n:read(E/n)['status'] for n in ['BUILD.json','COMPARATOR.json','KERNEL-REPLAY.json','AXIOM-AUDIT.json','SOURCE-AUDIT.json','ORIGINAL-SOURCE.json','DEPENDENCY-CHECK.json','CHALLENGE-PRECHECK.json']}
checks.update({c:v['status'] for c,v in vc.items()})
dump('RELEASE-CHECKS.json',checks)
print(json.dumps(checks),flush=True)
assert set(checks.values())=={'PASS'},checks
