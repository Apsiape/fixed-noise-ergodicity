import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resource_guard
resource_guard.guard()
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
import collections, hashlib, json, time
START = time.monotonic()
DEADLINE = START + 30.0
MAX_EVENTS = 1000000
# Atom names are represented by R0..R3=0..3, G0..G3=4..7.
THIN = ((0,6,1,7),(4,2,5,3),(2,4,7,1),(6,0,3,5)) # N,S,E,W
CORNER = (THIN[3], THIN[0], THIN[2], THIN[1])
BLACK = ((0,1,0,1),(1,0,0,0),(1,0,1,1),(1,1,1,0),(0,0,1,0))
KS = [('C',c) for c in range(4)] + [('L',v,h) for v in (0,2,4,6) for h in (1,3,5,7)]
def kedges(k):
    return CORNER[k[1]] if k[0]=='C' else (k[1],k[1],k[2],k[2])
def base_ok(t,k,b):
    if k[0]=='C':
        return t in (0,1) and b==0
    v,h=k[1:]
    eb=(b==1 and v!=0)
    ec=(b==2 and v!=2)
    ed=(b==3 and h!=3)
    ee=(b==4 and h!=1)
    return (t==0 and (eb or ec or ed or ee)) or (t==2 and (eb or ec)) or (t==3 and (ed or ee))
A=[]
for t in range(4):
    for k in KS:
        for b in range(5):
            if not base_ok(t,k,b): continue
            for x in range(2):
                for y in range(2):
                    if t in (1,2) and x!=0: continue
                    if t in (1,3) and y!=0: continue
                    if k[0]=='C' and x!=y: continue
                    if k[0]=='L' and k[1]<4 and k[2]<4 and x==y: continue
                    A.append((t,k,b,x,y))
assert len(A)==276, len(A)
IDX={a:i for i,a in enumerate(A)}
FULL=(1<<len(A))-1
EDGES=[]
for t,k,b,x,y in A:
    ke=kedges(k)
    EDGES.append(tuple((THIN[t][d],ke[d],BLACK[b][d], x if d<2 else y) for d in range(4)))
# Directions N,S,E,W; each relation mask lists possible neighbor symbols.
OPP=(1,0,3,2)
EDGE_BUCKETS=[]
for d in range(4):
    buckets={}
    for i,edge in enumerate(EDGES): buckets[edge[d]]=buckets.get(edge[d],0)|(1<<i)
    EDGE_BUCKETS.append(buckets)
MASKS=[[EDGE_BUCKETS[OPP[d]].get(EDGES[i][d],0) for i in range(len(A))] for d in range(4)]
RELCOUNT=sum(mask.bit_count() for rows in MASKS for mask in rows)
print(json.dumps({'alphabet_cases':len(A),'directional_pair_cases':4*len(A)**2,'compatible_directional_pairs':RELCOUNT}), flush=True)
# Four finite-torus ordinary-AC cases; no substitution expansion is used.
TAU={(0,0):0,(1,0):2,(0,1):3,(1,1):1}
ALPHA=IDX[(0,('C',0),0,1,1)]
def make_control_patch(root_corner):
    outers=((3,('L',4,5),3,0,0),(0,('C',0),0,0,0),(2,('L',4,5),1,0,0),(1,('C',0),0,0,0))
    outer=outers[root_corner]
    def children(index):
        t,k,b,x,y=A[index]
        kn,ks,ke,kw=kedges(k)
        vals=((0,k,b,1-x,1-y),(2,('L',THIN[t][1],ke),(1,1,2,2,2)[b],0,1-y),(3,('L',kn,THIN[t][3]),(4,3,3,3,4)[b],1-x,0),(1,('C',(1,3,2,0)[t]),0,0,0))
        return tuple(IDX[v] for v in vals)
    w=[IDX[outer]];n=1
    for step in range(6):
        nn=2*n;out=[0]*(nn*nn)
        for yy in range(n):
            for xx in range(n):
                sw,se,nw,ne=children(w[yy*n+xx]);p=2*yy*nn+2*xx
                out[p]=sw;out[p+1]=se;out[p+nn]=nw;out[p+nn+1]=ne
        w=out;n=nn
    assert n==64
    for yy in range(n):
        for xx in range(n):
            p=yy*n+xx
            if xx+1<n:assert EDGES[w[p]][2]==EDGES[w[p+1]][3]
            if yy+1<n:assert EDGES[w[p]][0]==EDGES[w[p+n]][1]
    crop=[w[yy*n+xx] for yy in range(16,49) for xx in range(16,49)]
    assert A[crop[16*33+16]]==(0,('C',root_corner),0,1,1)
    return crop,outer
def palette_case(side,xy_fixed,pin_alpha,forbid00=False,wrap=True,root_corner=0,corner_only=False):
    entries=side*side*len(A)
    print(json.dumps({'preallocation_side':side,'xy_fixed':xy_fixed,'pin_alpha':pin_alpha,'forbid00_SW':forbid00,'forbid_only_corners':corner_only,'root_corner':root_corner,'wrap':wrap,'logical_domain_entries':entries,'relation_pair_bound':4*len(A)**2}),flush=True)
    domains=[]
    for yy in range(side):
        for xx in range(side):
            mask=0
            for i,(t,k,b,x,y) in enumerate(A):
                if t!=TAU[(xx%2,yy%2)]:continue
                if xy_fixed and (x!=1-(xx%2) or y!=1-(yy%2)):continue
                if forbid00 and t==0 and x==0 and y==0 and (not corner_only or k[0]=='C'):continue
                mask|=1<<i
            domains.append(mask)
    alpha_index=IDX[(0,('C',root_corner),0,1,1)]
    root_p=0 if wrap else (side//2)*side+(side//2)
    if pin_alpha:domains[root_p]=1<<alpha_index
    initial_entries=sum(mask.bit_count() for mask in domains)
    neighbors=[]
    for yy in range(side):
        for xx in range(side):
            if wrap:
                neighbors.append(((0,((yy+1)%side)*side+xx),(1,((yy-1)%side)*side+xx),(2,yy*side+(xx+1)%side),(3,yy*side+(xx-1)%side)))
            else:
                ns=[]
                if yy+1<side:ns.append((0,(yy+1)*side+xx))
                if yy>0:ns.append((1,(yy-1)*side+xx))
                if xx+1<side:ns.append((2,yy*side+xx+1))
                if xx>0:ns.append((3,yy*side+xx-1))
                neighbors.append(ns)
    queue=collections.deque(range(side*side));queued=[True]*(side*side)
    events=0;deleted=0
    while queue:
        p=queue.popleft();queued[p]=False
        old=domains[p];new=old
        for d,j in neighbors[p]:
            probe=new
            while probe:
                low=probe&-probe;i=low.bit_length()-1
                if not (MASKS[d][i]&domains[j]):new&=~low
                probe-=low
        if new!=old:
            domains[p]=new;events+=1;deleted+=old.bit_count()-new.bit_count()
            for _,j in neighbors[p]:
                if not queued[j]:queue.append(j);queued[j]=True
    control_word=None;control_outer=None
    if side==33 and not wrap and pin_alpha and not xy_fixed and not forbid00:
        control_word,control_outer=make_control_patch(root_corner)
        assert all((domains[p]>>control_word[p])&1 for p in range(side*side)), ('actual_word_control_lost',root_corner)
    canonical=[]
    for p,mask in enumerate(domains):
        vals=[]
        while mask:
            low=mask&-mask;i=low.bit_length()-1;vals.append(A[i]);mask-=low
        canonical.append({'position':[p%side,p//side],'symbols':vals})
    result={'side':side,'xy_fixed':xy_fixed,'pin_alpha':pin_alpha,'forbid00_SW':forbid00,'forbid_only_corners':corner_only,'root_corner':root_corner,'wrap':wrap,'logical_domain_entries':entries,'initial_entries_after_filters':initial_entries,'final_entries':sum(mask.bit_count() for mask in domains),'empty_sites':sum(not mask for mask in domains),'singleton_sites':sum(mask.bit_count()==1 for mask in domains),'count_histogram':dict(sorted(collections.Counter(mask.bit_count() for mask in domains).items())),'root_position':[root_p%side,root_p//side],'alpha_survives':bool(domains[root_p]&(1<<alpha_index)),'domain_sha256':hashlib.sha256(','.join(format(mask,'x') for mask in domains).encode('ascii')).hexdigest(),'events':events,'deleted_entries':deleted,'positive_control_word_checked':control_word is not None,'positive_control_word_cells':0 if control_word is None else len(control_word),'positive_control_outer':control_outer,'canonical_domains':canonical}
    print(json.dumps({k:v for k,v in result.items() if k!='canonical_domains'},sort_keys=True),flush=True)
    return result
RESULTS=[]
if '--critical-only' not in sys.argv:
    for side,pinned in ((2,False),(8,True)):
        for xy in (False,True):RESULTS.append(palette_case(side,xy,pinned))
    RESULTS.append(palette_case(8,False,True,True,True))
    RESULTS.append(palette_case(33,False,True,False,False))
    RESULTS.append(palette_case(33,False,True,True,False))
for corner in range(4):
    RESULTS.append(palette_case(33,False,True,False,False,corner,True))
    RESULTS.append(palette_case(33,False,True,True,False,corner,True))
with open(os.path.join(HERE,'ENGINE-PALETTE-A-critical-controls.results.json' if '--critical-only' in sys.argv else 'ENGINE-PALETTE-A-results.json'),'w',encoding='utf-8') as f:
    json.dump({'engine':'A','alphabet_cases':len(A),'directional_pair_cases':4*len(A)**2,'compatible_directional_pairs':RELCOUNT,'cases':RESULTS,'elapsed_seconds':time.monotonic()-START},f,indent=2)
print('FINISHED_CASE_COUNT',len(RESULTS),'ELAPSED_SECONDS',round(time.monotonic()-START,3),flush=True)



