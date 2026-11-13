"""Pack four public source folders, checking every file against public git blobs,
the release working tree and SHA256SUMS. Adapted from the natural-rule package.
No development or relay source tree is vendored. Run python -I -B.
"""
from pathlib import Path
import hashlib,io,json,re,subprocess,tarfile
R=Path(__file__).resolve().parents[1]
OUT=Path(r'\\wsl.localhost\lean-comparator\opt\forgetting-lower-arxiv-2026-11-12\inputs')
CORES={
 'ForgettingNaturalRule':('fixed-noise-ergodicity-release','lean-natural','v2.1.0','2.1.0','10.5281/zenodo.24178276'),
 'FixedNoiseErgodicity':('fixed-noise-ergodicity-release','lean','v2.1.0','2.1.0','10.5281/zenodo.24178276'),
 'UncomputableNoiseDiagram':('uncomputable-noise-diagram-release','lean','v1.3.0','1.3.0','10.5281/zenodo.24178271'),
 'UndecidablePhaseDiagram':('undecidable-phase-diagram-release','lean','v1.2.0','1.2.0','10.5281/zenodo.24144192')}
H=lambda b:hashlib.sha256(b).hexdigest()
def git(root,*args,text=True):
    b=subprocess.check_output(['git','--no-optional-locks',*args],cwd=root)
    return b.decode().strip() if text else b
receipt={'cores':{}}
for name,(repo,folder,tag,version,doi) in CORES.items():
    root=Path('C:/Infanox')/repo
    commit=git(root,'rev-parse','HEAD');tree=git(root,'rev-parse',commit+':'+folder)
    tagcommit=git(root,'rev-parse',tag+'^{commit}')
    tagtree=git(root,'rev-parse',tagcommit+':'+folder)
    assert tree==tagtree,(name,'public tag tree differs')
    cit=git(root,'show',commit+':CITATION.cff')
    cv=re.search(r'^version:\s*(\S+)',cit,re.M).group(1)
    cd=re.search(r'^doi:\s*"?([^"\s]+)',cit,re.M).group(1)
    assert cv==version,(name,cv)
    sums={}
    for l in git(root,'show',commit+':SHA256SUMS').splitlines():
        h,p=l.split(None,1)
        p=p.lstrip('*')
        if p.startswith(folder+'/'):sums[p[len(folder)+1:]]=h
    raw=git(root,'archive','--format=tar',commit,folder,text=False)
    files={};wt_diff=[];sum_diff=[]
    buf=io.BytesIO()
    epoch=int(git(root,'show','-s','--format=%ct',commit))
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r') as source,tarfile.open(fileobj=buf,mode='w') as tf:
        for member in source:
            if member.isdir():continue
            assert member.isfile(),(name,member.name,'non-file')
            rel=member.name[len(folder)+1:]
            assert rel and not rel.startswith('/') and '..' not in Path(rel).parts
            assert not any(x=='SEALED' or x.startswith(('QB-TRIAGE','SEALED-PREDICTIONS')) for x in Path(rel).parts)
            data=source.extractfile(member).read();h=H(data)
            files[rel]={'sha256':h,'bytes':len(data),'mode':oct(member.mode)}
            if not (root/folder/rel).is_file() or H((root/folder/rel).read_bytes())!=h:wt_diff.append(rel)
            if sums.get(rel)!=h:sum_diff.append(rel)
            ti=tarfile.TarInfo(rel);ti.size=len(data);ti.mode=member.mode;ti.mtime=epoch
            tf.addfile(ti,io.BytesIO(data))
    have={p.relative_to(root/folder).as_posix() for p in (root/folder).rglob('*') if p.is_file()}
    extra=sorted(have-set(files))
    assert not wt_diff and not sum_diff and not extra,(name,wt_diff,sum_diff,extra)
    packed=buf.getvalue();(OUT/('public-'+name+'.tar')).write_bytes(packed)
    rec={'release_repo':str(root).replace('\\','/'),'folder':folder,'commit':commit,
         'tag':tag,'tag_commit':tagcommit,'version':version,'doi':doi,
         'public_url':'https://github.com/Apsiape/'+repo.removesuffix('-release')+'/tree/'+tag+'/'+folder,
         'tree':tree,'tag_tree':tagtree,'tree_equals_tag':True,
         'citation_version':cv,'citation_doi':cd,'citation_doi_matches_requested':cd==doi,
         'working_tree_mismatches':wt_diff,'working_tree_extra':extra,
         'sha256sums_count':len(sums),'sha256sums_mismatches':sum_diff,
         'sha256sums_extra':sorted(set(sums)-set(files)),
         'tar':'public-'+name+'.tar','tar_sha256':H(packed),'file_count':len(files),'files':files}
    if name=='ForgettingNaturalRule':
        oldtree=git(root,'rev-parse','v2.0.0:'+folder)
        rec.update({'v2_0_0_tree':oldtree,'identical_to_v2_0_0':oldtree==tree})
        assert oldtree==tree
    receipt['cores'][name]=rec
    print(name,len(files),'files; public tree, working tree, SHA256SUMS: PASS; citation DOI match',cd==doi,flush=True)
txt=json.dumps(receipt,indent=2)+'\n'
(OUT/'public-cores-receipt.json').write_text(txt)
(R/'relay/public-cores-receipt.json').write_text(txt)
