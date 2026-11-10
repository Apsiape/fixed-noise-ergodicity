import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import resource_guard
GUARD = resource_guard.guard()
for thread_var in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[thread_var] = '1'
import json, time
print('GUARD', json.dumps(GUARD), flush=True)

# Engine B: packet-color masks and synchronous global sweeps.
# The alphabet is independently assembled from the analytical component table.
low_black = {'m':'bc','i':'bc','t':'c','e':'c','j':'c','h':'c','l':'b','f':'b','r':'b','g':'b','o':'bc','k':'bc','n':'bc','q':'bc','p':'bc','s':'bc'}
high_black = {'t':'de','e':'d','j':'de','h':'e','l':'de','f':'d','r':'de','g':'e','o':'de','k':'d','n':'de','q':'e','p':'de','s':'d','m':'de','i':'e'}
line_atoms = {'e':('r0','r1'),'f':('r2','r1'),'g':('r2','r3'),'h':('r0','r3'), 'i':('g0','r3'),'j':('r0','g1'),'k':('g2','r1'),'l':('r2','g3'), 'm':('g0','g1'),'n':('g2','g1'),'o':('g2','g3'),'p':('g0','g3'), 'q':('g2','r3'),'r':('r2','g1'),'s':('g0','r1'),'t':('r0','g3')}
base = set((t,k,'a') for t in 'ab' for k in 'abcd')
base.update((t,k,b) for t in 'ac' for k,bs in low_black.items() for b in bs)
base.update((t,k,b) for t in 'ad' for k,bs in high_black.items() for b in bs)
letters=[]
for t,k,b in sorted(base):
    for x in (0,1):
        for y in (0,1):
            if t in 'bc' and x: continue
            if t in 'bd' and y: continue
            if k in 'abcd' and x != y: continue
            if k in line_atoms and all(z[0]=='r' for z in line_atoms[k]) and x==y: continue
            letters.append((t,k,b,x,y))
number = {a:i for i,a in enumerate(letters)}
assert len(base)==104 and len(letters)==276
# All edge packets use E,N,W,S order here, intentionally different from engine A.
thin_codes={t:tuple(v) for t,v in zip('abcd',((1,1,2,2),(3,3,0,0),(2,0,1,3),(0,2,3,1)))}
black_codes={b:tuple(v) for b,v in zip('abcde',((0,0,1,1),(0,1,0,0),(1,1,1,0),(1,1,0,1),(1,0,0,0)))}
corner_codes={k:tuple(v) for k,v in zip('abcd',((0,2,3,1),(1,1,2,2),(2,0,1,3),(3,3,0,0)))}
vertical_code={'r0':1,'r2':0,'g0':3,'g2':2}
horizontal_code={'r1':1,'r3':0,'g1':3,'g3':2}
edges=[]
for t,k,b,x,y in letters:
    kc=corner_codes[k] if k in corner_codes else (horizontal_code[line_atoms[k][1]],vertical_code[line_atoms[k][0]],horizontal_code[line_atoms[k][1]],vertical_code[line_atoms[k][0]])
    edges.append(tuple((thin_codes[t][d],kc[d],black_codes[b][d],y if d in (0,2) else x) for d in range(4)))
# Substitution independently expressed as component tuple formulas.
new_v=dict(zip('abcd',('g2','r2','g0','r0')))
new_h=dict(zip('abcd',('g3','r3','r1','g1')))
old_v=dict(zip('abcd',('g2','r0','r2','g0')))
old_h=dict(zip('abcd',('r3','r1','g3','g1')))
corner_ne=dict(zip('abcd','bdca'))
line_for={p:k for k,p in line_atoms.items()}
black_quad={'a':'abea','b':'bbda','c':'ccda','d':'dcda','e':'ecea'}
children=[]
for t,k,b,x,y in letters:
    va,ha=line_atoms[k] if k in line_atoms else (old_v[k],old_h[k])
    ks=(k,line_for[(new_v[t],ha)],line_for[(va,new_h[t])],corner_ne[t])
    bits=((1-x,1-y),(0,1-y),(1-x,0),(0,0))
    children.append(tuple(number[(tt,kk,bb,xx,yy)] for tt,kk,bb,(xx,yy) in zip('acdb',ks,black_quad[b],bits)))
assert len(set(edges))==276
opp=(2,3,0,1)
step=((1,0),(0,1),(-1,0),(0,-1))
for a,cs in enumerate(children):
    sw,se,nw,ne=cs
    assert edges[sw][0]==edges[se][2] and edges[nw][0]==edges[ne][2]
    assert edges[sw][1]==edges[nw][3] and edges[se][1]==edges[ne][3]
# Finite color classes: equal packet colors, no dense pair-table allocation.
color_masks=[{} for d in range(4)]
for a,es in enumerate(edges):
    for d,c in enumerate(es): color_masks[d][c]=color_masks[d].get(c,0)|(1<<a)
ALL=(1<<len(letters))-1

def values(mask):
    while mask:
        b=mask & -mask
        yield b.bit_length()-1
        mask-=b

PACKET_CACHE={}
def packet_support(mask):
    if mask not in PACKET_CACHE:
        support=[0,0,0,0]
        for a in values(mask):
            for d in range(4):
                support[d] |= color_masks[d].get(edges[a][opp[d]],0)
        PACKET_CACHE[mask]=tuple(support)
    return PACKET_CACHE[mask]

def make_word(power):
    rows=[[number[('a','a','a',1,1)]]]
    for _ in range(2*power):
        fine=[]
        for row in rows:
            south=[]; north=[]
            for a in row:
                sw,se,nw,ne=children[a]
                south.extend((sw,se)); north.extend((nw,ne))
            fine.extend((south,north))
        rows=fine
    return rows

def propagate(n,pinned):
    side=4**(n+1)
    cells=side*side
    print('SIZE_BEFORE_ALLOCATION',json.dumps({'engine':'B','N':n,'pins':pinned,'side':side,'position_cells':cells,'unary_domain_entries':cells*len(letters),'color_class_masks':sum(len(z) for z in color_masks),'maximum_directed_grid_arcs':4*cells,'not_a_token_tuple_table':True}),flush=True)
    word=make_word(n+1)
    truth=[a for row in word for a in row]
    for yy in range(side):
        for xx in range(side):
            a=word[yy][xx]
            if xx+1<side: assert edges[a][0]==edges[word[yy][xx+1]][2]
            if yy+1<side: assert edges[a][1]==edges[word[yy+1][xx]][3]
    domains=[ALL]*cells
    far=4**n
    if pinned:
        domains[0]=1<<truth[0]
        domains[far*side+far]=1<<truth[far*side+far]
    started=time.monotonic(); sweeps=0; changes=0
    while True:
        sweeps+=1
        # Snapshot color sets for each direction and each site; at most4*L²
        # small finite packet sets, estimated well below the guard's1GB cap.
        palettes=[packet_support(mask) for mask in domains]

        fresh=domains.copy(); changed=0
        for yy in range(side):
            for xx in range(side):
                pos=yy*side+xx
                keep=domains[pos]
                for d,(dx,dy) in enumerate(step):
                    nx=xx+dx; ny=yy+dy
                    if nx<0 or nx>=side or ny<0 or ny>=side: continue
                    keep &= palettes[ny*side+nx][d]

                assert keep & (1<<truth[pos]), ('truth_removed',n,pinned,xx,yy)
                if keep != domains[pos]: changed+=1
                fresh[pos]=keep
        domains=fresh; changes+=changed
        if not changed: break
        if sweeps>=200 or time.monotonic()-started>90:
            raise RuntimeError('bounded sweep/time cap; no fixedpoint claimed')
    target_side=4**(n-1)
    target=[yy*side+xx for yy in range(target_side) for xx in range(target_side)]
    def stats(indices):
        total=singles=meta_singles=0
        for p in indices:
            total+=domains[p].bit_count()
            singles += domains[p].bit_count()==1
            meta_singles += len({letters[a][1:] for a in values(domains[p])})==1
        return {'sites':len(indices),'entries':total,'singleton_tiles':singles,'singleton_KBXY':meta_singles}
    if pinned:
        ambiguities=[]
        for p,mask in enumerate(domains):
            if mask.bit_count()>1:
                ambiguities.append({'position':[p%side,p//side],'candidates':[letters[a] for a in values(mask)],'actual':letters[truth[p]]})
        with open(os.path.join(HERE,'ENGINE-AC-B-ambiguities-N'+str(n)+'.json'),'w',encoding='utf-8') as out:
            json.dump({'N':n,'side':side,'ambiguities':ambiguities},out,indent=2)
    result={'engine':'B','N':n,'pins':pinned,'cases':1,'side':side,'sweeps':sweeps,'changed_site_rounds':changes,'all_sites':stats(list(range(cells))),'SW_selected_block':stats(target),'pin_letters':[letters[truth[0]],letters[truth[far*side+far]]],'every_truth_entry_survived':True,'wall_seconds':round(time.monotonic()-started,3)}
    print('CASE_RESULT',json.dumps(result),flush=True)
    return result

def actual_control_patch(corner):
    roots={'a':('d','m','d',0,0),'b':('a','a','a',0,0),'c':('c','m','b',0,0),'d':('b','a','a',0,0)}
    rows=[[number[roots[corner]]]]
    for _ in range(6):
        fine=[]
        for row in rows:
            south=[];north=[]
            for a in row:
                sw,se,nw,ne=children[a]
                south.extend((sw,se));north.extend((nw,ne))
            fine.extend((south,north))
        rows=fine
    out=[rows[y][x] for y in range(16,49) for x in range(16,49)]
    assert letters[out[16*33+16]]==('a',corner,'a',1,1)
    for y in range(33):
        for x in range(33):
            a=out[y*33+x]
            if x+1<33: assert edges[a][0]==edges[out[y*33+x+1]][2]
            if y+1<33: assert edges[a][1]==edges[out[(y+1)*33+x]][3]
    return out

def corner_case(corner,forbid):
    side=33;center=16
    print('CORNER_SIZE_BEFORE_ALLOCATION',json.dumps({'side':side,'corner':corner,'forbid00SWcorner':forbid,'position_cells':1089,'unary_entries_bound':300564}),flush=True)
    domain=[]
    for yy in range(side):
        for xx in range(side):
            t='acdb'[2*(yy%2)+(xx%2)]
            mask=0
            for a,l in enumerate(letters):
                if l[0]!=t: continue
                if forbid and l[0]=='a' and l[1] in 'abcd' and l[3]==l[4]==0: continue
                mask |= 1<<a
            domain.append(mask)
    root=number[('a',corner,'a',1,1)]
    domain[center*side+center] &= 1<<root
    rounds=0;first_root_empty=None
    while True:
        rounds+=1;supported=[packet_support(m) for m in domain];new=[]
        for yy in range(side):
            for xx in range(side):
                mask=domain[yy*side+xx]
                for d,(dx,dy) in enumerate(step):
                    nx=xx+dx;ny=yy+dy
                    if nx<0 or nx>=side or ny<0 or ny>=side: continue
                    mask &= supported[ny*side+nx][d]
                new.append(mask)
        if new[center*side+center]==0 and first_root_empty is None: first_root_empty=rounds
        if new==domain: break
        domain=new
        if rounds>1000: raise RuntimeError('round cap')
    result={'corner':corner,'forbid00SWcorner':forbid,'side':side,'root_position':[16,16],'cases':1,'rounds':rounds,'first_root_empty':first_root_empty,'empty_sites':sum(m==0 for m in domain),'retained_entries':sum(m.bit_count() for m in domain),'root_candidates':domain[center*side+center].bit_count(),'domains':[[letters[a] for a in values(m)] for m in domain]}
    if not forbid:
        control=actual_control_patch(corner)
        assert all(mask & (1<<a) for mask,a in zip(domain,control)), 'known actual control patch removed'
        result['known_actual_control_patch_verified']=True
        assert result['empty_sites']==0, 'positive control failed'
    print('CORNER_RESULT',json.dumps({k:v for k,v in result.items() if k!='domains'}),flush=True)
    return result
results=[corner_case(c,f) for c in 'abcd' for f in (False,True)]
with open(os.path.join(HERE,'CORNERS-B-CONTROLS.results.json'),'w',encoding='utf-8') as out: json.dump({'guard':GUARD,'case_count':len(results),'results':results},out,indent=2)
print('COMPLETE_CORNER_CASES',len(results),flush=True)

