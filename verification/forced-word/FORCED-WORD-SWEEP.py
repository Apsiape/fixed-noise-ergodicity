import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import resource_guard
resource_guard.guard()
import json, time
from pathlib import Path

# Independent encoding from manuscript Appendix A; N,S,E,W order.
thin = {
 'a':('r0','g2','r1','g3'), 'b':('g0','r2','g1','r3'),
 'c':('r2','g0','g3','r1'), 'd':('g2','r0','r3','g1')}
corners = {'a':thin['d'], 'b':thin['a'], 'c':thin['c'], 'd':thin['b']}
black = {'A':(0,1,0,1),'B':(1,0,0,0),'C':(1,0,1,1),
         'D':(1,1,1,0),'E':(0,0,1,0)}
F={'a':'b','b':'d','c':'c','d':'a'}
se={'A':'B','B':'B','C':'C','D':'C','E':'C'}
nw={'A':'E','B':'D','C':'D','D':'D','E':'E'}
vs=('r0','r2','g0','g2'); hs=('r1','r3','g1','g3')
types=[('corner',c) for c in corners]+[('line',v,h) for v in vs for h in hs]
def edges_k(k):
    return corners[k[1]] if k[0]=='corner' else (k[1],k[1],k[2],k[2])
def permitted(t,k,b):
    if k[0]=='corner': return t in 'ab' and b=='A'
    if b=='A' or (t=='b') or (t=='c' and b not in 'BC') or (t=='d' and b not in 'DE'): return False
    return not ((b=='B' and k[1]=='r0') or (b=='C' and k[1]=='r2') or
                (b=='D' and k[2]=='r3') or (b=='E' and k[2]=='r1'))
letters=[]
bases=0
for t in 'abcd':
 for k in types:
  for b in 'ABCDE':
   if not permitted(t,k,b): continue
   bases+=1
   for x in (0,1):
    for y in (0,1):
     if t in 'bc' and x: continue
     if t in 'bd' and y: continue
     if k[0]=='corner' and x!=y: continue
     if k[0]=='line' and k[1][0]=='r' and k[2][0]=='r' and x==y: continue
     letters.append((t,k,b,x,y))
assert bases==104 and len(letters)==276
ids={a:i for i,a in enumerate(letters)}
colors=[]
for t,k,b,x,y in letters:
    colors.append(tuple((thin[t][d],edges_k(k)[d],black[b][d],x if d<2 else y) for d in range(4)))
opposite=(1,0,3,2)
groups=[]
for d in range(4):
    g={}
    for i,c in enumerate(colors): g[c[d]]=g.get(c[d],0)|(1<<i)
    groups.append(g)
thinmask={t:sum(1<<i for i,a in enumerate(letters) if a[0]==t) for t in 'abcd'}
parity={(0,0):'a',(1,0):'c',(0,1):'d',(1,1):'b'}
children=[]
for t,k,b,x,y in letters:
    ke=edges_k(k)
    child=(('a',k,b,1-x,1-y),
           ('c',('line',thin[t][1],ke[2]),se[b],0,1-y),
           ('d',('line',ke[0],thin[t][3]),nw[b],1-x,0),
           ('b',('corner',F[t]),'A',0,0))
    assert all(a in ids for a in child)
    c=tuple(ids[a] for a in child)
    assert colors[c[0]][2]==colors[c[1]][3] and colors[c[0]][0]==colors[c[2]][1]
    assert colors[c[1]][0]==colors[c[3]][1] and colors[c[2]][2]==colors[c[3]][3]
    children.append(c)
def letter_at(root,depth,x,y):
    for k in reversed(range(depth)):
        root=children[root][((x>>k)&1)+2*((y>>k)&1)]
    return root

# Independent color-group synchronous greatest-fixed-point engine:
# a group's color survives iff present in the neighbor's opposite edge colors.
def ac(box,pins,ban0=False):
    lo,hi=box; side=hi-lo+1
    domain=[thinmask[parity[(x%2,y%2)]] for y in range(lo,hi+1) for x in range(lo,hi+1)]
    if ban0:
        banned=sum(1<<i for i,a in enumerate(letters) if a[0]=='a' and a[1][0]=='corner' and a[3:]==(0,0))
        domain=[m&~banned for m in domain]
    for (x,y),i in pins.items():
        domain[(y-lo)*side+x-lo]&=1<<i
    # compatibility maps are independently assembled by matching group colors.
    relevant=[[(mask,groups[opposite[d]].get(c,0)) for c,mask in groups[d].items()] for d in range(4)]
    cache=[{} for d in range(4)]
    rounds=0; start=time.monotonic()
    while True:
        new=domain.copy(); changed=False
        for p,m in enumerate(domain):
            if not m: continue
            x=p%side; y=p//side
            for d,n in ((0,p+side),(1,p-side),(2,p+1),(3,p-1)):
                if (d==0 and y==side-1) or (d==1 and y==0) or (d==2 and x==side-1) or (d==3 and x==0): continue
                nb=domain[n]
                supported=cache[d].get(nb)
                if supported is None:
                    supported=0
                    for own,other in relevant[d]:
                        if nb&other: supported|=own
                    if len(cache[d])>50000: cache[d].clear()
                    cache[d][nb]=supported
                m&=supported
                if not m: break
            if m!=domain[p]: new[p]=m; changed=True
        domain=new; rounds+=1
        if not changed: break
    return domain,{'rounds':rounds,'sites':len(domain),'empty':sum(m==0 for m in domain),
                   'total_letters':sum(m.bit_count() for m in domain),
                   'seconds':round(time.monotonic()-start,3)}
def val(domain,box,x,y): return domain[(y-box[0])*(box[1]-box[0]+1)+x-box[0]]
def desc(i):
    a=letters[i]; return [a[0],list(a[1]),a[2],a[3],a[4]]
def verify_control(domain,box,root,depth,offset):
    # Every retained value of an independently generated legal word is checked.
    for y in range(box[0],box[1]+1):
     for x in range(box[0],box[1]+1):
      a=letter_at(root,depth,offset[0]+x,offset[1]+y)
      assert val(domain,box,x,y)&(1<<a),('legal control lost',x,y,desc(a))
      if x<box[1]:
          east=letter_at(root,depth,offset[0]+x+1,offset[1]+y)
          assert colors[a][2]==colors[east][3],('control horizontal seam',x,y)
      if y<box[1]:
          north=letter_at(root,depth,offset[0]+x,offset[1]+y+1)
          assert colors[a][0]==colors[north][1],('control vertical seam',x,y)
def target_errors(domain,box,pin,n):
    N=4**n; count=0; nonempty=0
    for y in range(N):
     for x in range(N):
      m=val(domain,box,x,y); expected=letter_at(pin,2*n,x,y)
      count+=m!=(1<<expected); nonempty+=bool(m)
    return count,nonempty

root=ids[('a',('corner','a'),'A',0,0)]
# Choose a legal interior coarse corner11 with diagonal corner00.
pair=None
for y in range(3,60):
 for x in range(3,60):
    p=letter_at(root,6,x,y); q=letter_at(root,6,x+1,y+1)
    if letters[p][0]=='a' and letters[p][1][0]=='corner' and letters[p][3:]==(1,1) and letters[q][1][0]=='corner' and letters[q][3:]==(0,0):
        pair=(x,y,p,q); break
 if pair: break
assert pair
cx,cy,coarse_plus,coarse_minus=pair
print(json.dumps({'alphabet':len(letters),'base_count':bases,'coarse_control_pair':[cx,cy,desc(coarse_plus),desc(coarse_minus)]}),flush=True)
results=[]
mode=sys.argv[1] if len(sys.argv)>1 else 'all'
ns=(1,2,3) if mode=='all' else (int(mode),)
for n in ns:
 N=4**n; box=(-N,2*N-1)
 plus=letter_at(coarse_plus,2*n,0,0); minus=letter_at(coarse_minus,2*n,0,0)
 assert letters[plus][3:]==(1,1) and letters[minus][3:]==(0,0)
 pins={(0,0):plus,(N,N):minus}
 domain,stats=ac(box,pins)
 errors,filled=target_errors(domain,box,plus,n)
 verify_control(domain,box,root,2*n+6,(cx*N,cy*N))
 assert stats['empty']==0 and errors==0,('forced-word mismatch',n,stats,errors)
 row={'kind':'nonvacuous_forced_word','n':n,'N':N,'box':box,'pins':[[0,0,desc(plus)],[N,N,desc(minus)]],
      'target_sites':N*N,'target_errors':errors,'legal_control_sites':stats['sites'],**stats}
 results.append(row); print(json.dumps(row),flush=True)
 # Pin ablation is a sensitivity control: it must preserve the legal word;
 # non-singletons diagnose whether the second pin supplied actual information.
 d2,s2=ac(box,{(0,0):plus})
 e2,_=target_errors(d2,box,plus,n)
 verify_control(d2,box,root,2*n+6,(cx*N,cy*N))
 row={'kind':'remove_zero_pin','n':n,'target_nonsingletons_or_wrong':e2,**s2}
 results.append(row); print(json.dumps(row),flush=True)
 if n<=2:
  # All16 thick-orientation pairs on a diagonal, including inconsistent pairs.
  for ca in 'abcd':
   for cb in 'abcd':
    pi=ids[('a',('corner',ca),'A',1,1)]; mi=ids[('a',('corner',cb),'A',0,0)]
    dd,ss=ac(box,{(0,0):pi,(N,N):mi})
    ee,ff=target_errors(dd,box,pi,n)
    assert ss['empty']==ss['sites'] or (ss['empty']==0 and ee==0),('unresolved orientation',n,ca,cb,ss,ee)
    row={'kind':'orientation_pair','n':n,'plus_corner':ca,'minus_corner':cb,'target_errors':ee,**ss}
    results.append(row); print(json.dumps(row),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps({'encoding':'independent color groups, synchronous sweeps, open box',
 'results':results,'scope':'Finite greatest arc-consistent subfamilies only. Nonempty fixed point does not prove global extension. Nonvacuous cases certified by retained legal substitution word. No full-token-game test and no all-n proof.'},indent=2))
print('PASS',flush=True)


