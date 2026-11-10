import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import resource_guard
resource_guard.guard()
import json, time, hashlib
from collections import deque
from functools import lru_cache

# Independent direct transcription of Appendix tables, in N,S,E,W order.
THIN = {'a': ('r0','g2','r1','g3'), 'b': ('g0','r2','g1','r3'),
        'c': ('r2','g0','g3','r1'), 'd': ('g2','r0','r3','g1')}
CORNER = {'a': ('g2','r0','r3','g1'), 'b': ('r0','g2','r1','g3'),
          'c': ('r2','g0','g3','r1'), 'd': ('g0','r2','g1','r3')}
BLACK = {'A': (0,1,0,1), 'B': (1,0,0,0), 'C': (1,0,1,1),
         'D': (1,1,1,0), 'E': (0,0,1,0)}
F = {'a':'b','b':'d','c':'c','d':'a'}
SE = {'A':'B','B':'B','C':'C','D':'C','E':'C'}
NW = {'A':'E','B':'D','C':'D','D':'D','E':'E'}
TILES=[]
for th in 'abcd':
    bases=[]
    if th in 'ab':
        bases.extend((k,'A') for k in CORNER)
    if th in 'ac': blacks='BC'
    elif th=='d': blacks='DE'
    else: blacks=''
    for bl in blacks:
        for v in ('r0','r2','g0','g2'):
            for h in ('r1','r3','g1','g3'):
                if bl=='B' and v=='r0': continue
                if bl=='C' and v=='r2': continue
                if bl=='D' and h=='r3': continue
                if bl=='E' and h=='r1': continue
                bases.append(((v,h),bl))
    # thin a has both line classes
    if th=='a':
        for bl in 'DE':
            for v in ('r0','r2','g0','g2'):
                for h in ('r1','r3','g1','g3'):
                    if bl=='D' and h=='r3': continue
                    if bl=='E' and h=='r1': continue
                    bases.append(((v,h),bl))
    for k,bl in bases:
        for b1 in (0,1):
            for b2 in (0,1):
                if th in 'bc' and b1: continue
                if th in 'bd' and b2: continue
                if isinstance(k,str) and b1!=b2: continue
                if isinstance(k,tuple) and k[0][0]=='r' and k[1][0]=='r' and b1==b2: continue
                TILES.append((th,k,bl,b1,b2))
assert len(TILES)==276 and len(set(TILES))==276
INDEX={t:i for i,t in enumerate(TILES)}
EDGES=[]
for th,k,bl,b1,b2 in TILES:
    kedge=CORNER[k] if isinstance(k,str) else (k[0],k[0],k[1],k[1])
    EDGES.append(tuple((THIN[th][d],kedge[d],BLACK[bl][d], (b1 if d<2 else b2)) for d in range(4)))
OPP=(1,0,3,2)
DELTA=((0,1),(0,-1),(1,0),(-1,0))
GROUPS=[]
for d in range(4):
    by={}
    for i,e in enumerate(EDGES): by[e[d]]=by.get(e[d],0)|(1<<i)
    GROUPS.append(by)
PAIRCOUNT=sum(sum((GROUPS[OPP[d]].get(e[d],0)).bit_count() for e in EDGES) for d in range(4))
assert PAIRCOUNT==4496
PHASE={}
for x in (0,1):
    for y in (0,1):
        th={(0,0):'a',(1,0):'c',(0,1):'d',(1,1):'b'}[x,y]
        PHASE[x,y]=sum(1<<i for i,t in enumerate(TILES) if t[0]==th)

@lru_cache(maxsize=100000)
def support(d, neighbor_mask):
    result=0
    for color, source_mask in GROUPS[d].items():
        if GROUPS[OPP[d]].get(color,0)&neighbor_mask: result|=source_mask
    return result

def subst(tile):
    th,k,bl,b1,b2=tile
    ke=CORNER[k] if isinstance(k,str) else (k[0],k[0],k[1],k[1])
    return {(0,0):('a',k,bl,1-b1,1-b2),
            (1,0):('c',(THIN[th][1],ke[2]),SE[bl],0,1-b2),
            (0,1):('d',(ke[0],THIN[th][3]),NW[bl],1-b1,0),
            (1,1):('b',F[th],'A',0,0)}

def word(tile, depth):
    out={(0,0):tile}
    for _ in range(depth):
        nxt={}
        for (x,y),t in out.items():
            for (dx,dy),s in subst(t).items():
                assert s in INDEX
                nxt[2*x+dx,2*y+dy]=s
        out=nxt
    return out

def legal(w):
    for (x,y),t in w.items():
        for d,(dx,dy) in enumerate(DELTA):
            other=w.get((x+dx,y+dy))
            if other is not None: assert EDGES[INDEX[t]][d]==EDGES[INDEX[other]][OPP[d]]


def solve(n,k1,k0,w=(1,1),ablate=False,witness=None):
    N=4**n; ax,ay=N*w[0],N*w[1]
    lo_x=min(-N,ax-N); hi_x=max(2*N,ax+N)
    lo_y=min(-N,ay-N); hi_y=max(2*N,ay+N)
    width=hi_x-lo_x+1; height=hi_y-lo_y+1; count=width*height
    def ix(x,y): return (y-lo_y)*width+x-lo_x
    domains=[PHASE[(x+lo_x)%2,(y+lo_y)%2] for y in range(height) for x in range(width)]
    domains[ix(0,0)]=1<<INDEX['a',k1,'A',1,1]
    if not ablate: domains[ix(ax,ay)]=1<<INDEX['a',k0,'A',0,0]
    queue=deque(range(count)); queued=bytearray(b'\1')*count
    visits=0; changes=0; start=time.monotonic()
    while queue:
        q=queue.popleft(); queued[q]=0; visits+=1
        x=q%width; y=q//width; old=domains[q]; new=old
        if y+1<height: new&=support(0,domains[q+width])
        if y>0: new&=support(1,domains[q-width])
        if x+1<width: new&=support(2,domains[q+1])
        if x>0: new&=support(3,domains[q-1])
        if new==old: continue
        domains[q]=new; changes+=1
        neigh=[]
        if y+1<height: neigh.append(q+width)
        if y>0: neigh.append(q-width)
        if x+1<width: neigh.append(q+1)
        if x>0: neigh.append(q-1)
        for p in neigh:
            if not queued[p]: queue.append(p); queued[p]=1
    target=word(('a',k1,'A',1,1),2*n); legal(target)
    wrong=[]; nonsingle=0
    for (x,y),t in target.items():
        mask=domains[ix(x,y)]
        if mask.bit_count()!=1: nonsingle+=1
        if mask!=(1<<INDEX[t]): wrong.append((x,y,mask.bit_count()))
    empty=sum(mask==0 for mask in domains)
    losses=0
    if witness is not None:
        for y in range(lo_y,hi_y+1):
            for x in range(lo_x,hi_x+1):
                t=witness[x,y]
                if not domains[ix(x,y)]&(1<<INDEX[t]): losses+=1
        assert losses==0
    h=hashlib.sha256()
    for mask in domains: h.update(mask.to_bytes(35,'little'))
    result=dict(n=n,corner11=k1,corner00=k0,displacement=[ax,ay],box=[lo_x,hi_x,lo_y,hi_y],ablate=ablate,
                sites=count,empty_sites=empty,total_values=sum(m.bit_count() for m in domains),
                target_wrong=len(wrong),target_nonsingleton=nonsingle,first_wrong=wrong[:4],
                witness_cells=(count if witness is not None else 0),witness_losses=losses,
                visits=visits,changes=changes,seconds=round(time.monotonic()-start,4),domain_sha256=h.hexdigest())
    print(json.dumps(result),flush=True)
    return result

results=[]
# Nonvacuous independent controls taken from a generated legal substitution word.
coarse=word(('a','a','A',1,1),4);legal(coarse)
for n in (1,2,3):
    N=4**n
    candidates=[]
    for y in range(1,14):
        for x in range(1,14):
            a=coarse[x,y]; b=coarse[x+1,y+1]
            if a[0]=='a' and isinstance(a[1],str) and a[3:]==(1,1) and isinstance(b[1],str) and b[3:]==(0,0):
                candidates.append((x,y,a,b))
    assert candidates
    x0,y0,a,b=candidates[0]
    full=word(('a','a','A',1,1),2*n+4);legal(full)
    patch={(x-N*x0,y-N*y0):t for (x,y),t in full.items() if -N<=x-N*x0<=2*N and -N<=y-N*y0<=2*N}
    legal(patch)
    assert patch[0,0]==a and patch[N,N]==('a',b[1],'A',0,0)
    positive=solve(n,a[1],b[1],witness=patch)
    assert positive['empty_sites']==0 and positive['target_wrong']==0
    results.append(positive)
    ablated=solve(n,a[1],b[1],ablate=True,witness=patch)
    assert ablated['empty_sites']==0 and ablated['target_nonsingleton']>0
    results.append(ablated)
    del full,patch
    # All corner orientations on a nearest diagonal detector; AC-empty cases are marked vacuous.
    if n<=2:
        for ka in 'abcd':
            for kb in 'abcd':
                r=solve(n,ka,kb)
                assert r['empty_sites'] or r['target_wrong']==0
                results.append(r)
out=dict(engine='independent-manuscript-bitset-queue',alphabet=276,paircount=PAIRCOUNT,results=results,
         limitation='Finite nonwrapping AC sufficient certificates on listed boxes only. Does not prove all n, arbitrary displacements, or plane-safe-state realizability.')
Path(__file__).with_suffix('.results.json').write_text(json.dumps(out,indent=2))
print('COMPLETE',len(results),flush=True)

