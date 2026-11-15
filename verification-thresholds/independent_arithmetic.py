from fractions import Fraction as Q
from math import comb, factorial
from itertools import product

# Preflight: all finite arrays are bounded before creation. No lattice BFS or DAG search.
# Largest small array: <= 200 scalar check results; corners <= 80*5 gain integers;
# degree polynomial <= 8 entries; TI stencil <= 60 vectors of length 7.
# Largest exponentiation operands: < 2,000,000 bits each (< 250,000 bytes each).
# At most 20 simultaneous big integers, conservative numerical working set < 64 MiB.
print('PRECHECK: <=200 checks; <=400 corner gains; 8 polynomial entries; 60x7 stencil; <64 MiB numerical work.')
checks = 0
def ck(label, condition):
    global checks
    checks += 1
    assert condition, label
    print('OK', label)
def val(label, q):
    print('VALUE', label, format(float(q), '.14g'))

def eulerian(n):
    # Derive numerator from applying y*d/dy+1 to sum (r+1)^(n-1)y^r.
    a = [1]
    for m in range(1, n+1):
        out = [0]*(len(a)+1)
        for j, c in enumerate(a):
            out[j] += (j+1)*c
            out[j+1] += (m-j-1)*c
        while len(out)>1 and out[-1]==0:
            out.pop()
        a = out
    return a
A5, A7 = eulerian(5), eulerian(7)
ck('A5 derived by differentiation', A5 == [1,26,66,26,1])
ck('A7 derived by differentiation', A7 == [1,120,1191,2416,1191,120,1])
ck('Eulerian sums', sum(A5)==factorial(5) and sum(A7)==factorial(7))
def zhat(k, y):
    a, den = (A7,8) if k==4 else (A5,6)
    return 4*175**k*sum(c*y**j for j,c in enumerate(a))/(1-y)**den

# Independent corner evaluation: affine gains attain extrema on box corners.
def gains(k, slope, per_time):
    all_min, good_min = None, None
    for cluster in range(k+1):
        for corner in product((0,15), repeat=k):
            a = tuple(corner[j]+(160 if cluster==j+1 else 0) for j in range(k))
            g = (slope*sum(a)-k*per_time,)+tuple(per_time-slope*x for x in a)
            ck_dummy = sum(g)
            assert ck_dummy == 0
            for charge,x in enumerate(g):
                all_min = x if all_min is None else min(all_min,x)
                if charge!=cluster:
                    good_min = x if good_min is None else min(good_min,x)
    return good_min, -all_min
old6 = gains(4,5,160)
new6 = gains(4,4,140)
z4 = gains(2,3,175)
ck('old Z6 drift floors', old6==(85,715))
ck('new Z6 drift floors', new6==(80,560))
ck('Z4 drift floors', z4==(130,350))
ck('old Z6 coefficient', Q(5*(85+715),85)==Q(4000,85)<50)
ck('old Z4 coefficient', Q(3*(130+350),130)==Q(144,13)<12)
ck('new Z6 coefficient', 5-Q(3*80-2*560,80)==16)
ck('new Z4 coefficient', 3-Q(130-2*350,130)==Q(96,13))
ck('Z6 walk/connector budgets', 2*16==32 and 3*16==48)
alpha=Q(96,13); delta=Q(1,1404)
ck('Z4 geometry and packing', 4*(350+1)==1404 and alpha/delta==10368 and 2*alpha<15)
ck('Z4 weighted exponent', 15+10368==10383)
ck('Z6 q and degree', 5*16**4==327680 and 18*5*16**4==5898240)
ck('Z4 q and old B', 3*16**2==768 and 2*(18*768)**2==382205952)

ck('Z6 overlap and mortality arithmetic',5*15*16**3>4*16**4 and 2*160+4*15==380 and 2*(380+1)+0==762)
ck('Z4 overlap arithmetic',3*15*16==720>2*256 and 2*175==350)
ck('rounded Z6 sparse factors imply lambda',2*Q(1,10**24)*Q(2043,1000)*10**18*2313<=Q(95,10**4))
ck('rounded Z6 path factors imply kappa',Q(1,10**24)*Q(433,100)*10**19*2586<Q(1,8))
ck('rounded Z4 factors imply kappa',Q(1,10**30)*Q(3857,1000)*10**26*Q(41319,100)<=Q(1594,10000))
ck('ND weakened density endpoint',Q(16,3)<6 and Q(1)>Q(1,4212))

E6=Q(1,10**24); y=Q(785,1000); Z=zhat(4,y)
lam=2*E6*Z*y**-32
p=2*E6+2*E6*Z*lam/(1-lam)
ck('Z6 sparse displayed Z upper', Z<=Q(2043,1000)*10**18)
ck('Z6 sparse displayed power upper', y**-32<=2313)
ck('Z6 lambda bound', lam<=Q(95,10**4))
ck('Z6 crude memory < 1e-4', 2*E6+Q(95,10**4)**2/(1-Q(95,10**4))<Q(1,10**4))
ck('Z6 actual rational memory < 3.9e-8', p<Q(39,10**9))
ck('Z6 optional 4e-8 bound', p<=Q(4,10**8))
ck('memory separation > 1/2', 1-2*Q(1,10**4)>Q(1,2))
val('Z6 lambda at 2e-24',lam); val('Z6 p at 2e-24',p)
y=Q(5,8); Z=zhat(4,y); small=Q(1,10**40); lam=small*Z*y**-32
ck('Z6 recovery at 1e-40',lam<1 and Z*lam/(1-lam)<1)
y=Q(849,1000); Z=zhat(4,y); kap=E6*Z*y**-48
ck('Z6 path displayed Z upper', Z<=Q(433,100)*10**19)
ck('Z6 path displayed power upper', y**-48<=2586)
ck('Z6 path base <= 1/8', kap<=Q(1,8))
ck('Z6 robustness base <= 1/4', 2*kap<=Q(1,4))
val('Z6 kappa at 1e-24',kap)
ck('coalescence prefactor 8/7',1/(1-Q(1,8))==Q(8,7))
ck('coalescence c factor',Q(3,16)==Q(1,16)*3)
ck('robust slope log2/8',Q(2,16)==Q(1,8))
ck('old Z6 interval included', (2*(18*5*16**4)**2)**200>=10**24)

E4=Q(1,10**30); y=Q(1,2); Z=zhat(2,y); lam=E4*Z*y**-15
ck('Z4 exact Zhalf',Z==265090000)
ck('Z4 lambda < 1e-17',lam<Q(1,10**17))
ck('Z4 sparse < 2e',Z*lam/(1-lam)<1)
val('Z4 lambda',lam); val('Z4 excess divided by e',Z*lam/(1-lam))

# exp(1) is bracketed from its factorial series and an explicit geometric tail.
N=16
esum=sum((Q(1,factorial(i)) for i in range(N+1)), Q(0))
ehi=esum+Q(1,factorial(N+1))/(1-Q(1,N+2))
Eupper=Q(27183,10000)
ck('analytic e upper certificate',ehi<Eupper<3)
y=Q(99942,100000); Z=zhat(2,y); kap=E4*Z*y**-10383; mu=E4*Z*y**-15
ck('Z4 large interval displayed Z',Z<=Q(3857,1000)*10**26)
ck('Z4 large interval displayed power',y**-10383<=Q(41319,100))
ck('Z4 small walk power',y**-15<=Q(101,100))
ck('Z4 kappa <= .1594',kap<=Q(1594,10000))
ck('Z4 mu < .00039',mu<Q(39,100000))
ck('Z4 mu <= 1/2',mu<=Q(1,2))
# No logarithm or floating point used in exponent certification.
ck('Z4 rho < exp(-1/6000)',Q(1594,10000)**6000 * Eupper**10368 < 1)
val('Z4 kappa at 1e-30',kap); val('Z4 mu at 1e-30',mu)
y=Q(999422,10**6); Z=zhat(2,y); tiny=Q(1,10**4535)
kap=tiny*Z*y**-10383; mu=tiny*Z*y**-15
ck('tiny interval rho <= exp(-1)',kap<=Eupper**-10368)
ck('tiny interval mu <= 1/16',mu<=Q(1,16))
ck('tiny density prefactor <= 16/15',1/(1-mu)<=Q(16,15)<Q(16,3))
ck('old lower interval below 1e-4535',382205952**33720>=10**4535)
ck('U case I covers 701b',Q(6000,5299)<2)
ck('U case II covers constants',Q(16,3)<6 and Eupper<3)
ck('floor case I multiplier <4',2*Q(12000,11999)<4)
ck('floor case II multiplier <16',Q(16,3)*2<16) # exp(.5) <= 2
ck('rates from gamma/4',Q(1,6000)/4==Q(1,24000) and Q(1)/4==Q(1,4))
ck('polynomial maxima',20/Q(1,6000)==120000 and 20/Q(1)==20)
ck('maximum correction <=0',all(-5+g/4<=0 for g in (Q(1,6000),Q(1))))
ck('small t prefactor',4>Q(4,3) and Eupper<3) # 4 exp(-1/4)>1 since exp(1/4)<4/3
ck('cone coefficient',175**2==30625)
ck('fixed geometric inequalities',3*15*16==720>2*256 and 700==2*350 and 702==2*351)

# Fixed-rate graph, independently formed from the specified 12-parent checker.
# Table size fixed at <=60 vectors of length 7, <10KiB.
zero4=(0,0,0,0)
N0=[(0,0),(-1,-1),(0,-1),(1,-1)]
stencil=[(u,zero4) for u in N0]
for l in range(4):
    for sign in (-1,1):
        n=list(zero4); n[l]=sign; stencil.append(((0,0),tuple(n)))
steps=[]
for provider in range(5):
    for u,n in stencil:
        a=tuple(n[l]+(10 if provider==l+1 else 0) for l in range(4))
        steps.append(u+a+(-1,))
ck('TI 60 distinct steps',len(steps)==60 and len(set(steps))==60)
ck('TI coordinate budgets',all(max(abs(s[0]),abs(s[1]))<=1 and sum(abs(x) for x in s[2:6])<=11 for s in steps))
ck('TI original gains',all(min((10*(provider>0)+sum(n)-8,)+tuple(2-10*(provider==l+1)-n[l] for l in range(4)))>=-9 for provider in range(5) for _,n in stencil))
ck('TI good gains',all(g>=1 for provider in range(5) for _,n in stencil for charge,g in enumerate((10*(provider>0)+sum(n)-8,)+tuple(2-10*(provider==l+1)-n[l] for l in range(4))) if charge!=provider))
ck('TI arm50 and walk150',5*(1+9)==50 and 2*50==100 and 3*50==150)
def l1four(R):
    return sum(2**j*comb(4,j)*comb(R,j) for j in range(min(4,R)+1))
def b(r): return (2*r+1)**3*l1four(11*r)
# Eight forward differences determine a degree-seven polynomial exactly.
row=[b(r) for r in range(8)]
D=[]
for _ in range(8):
    D.append(row[0]); row=[row[i+1]-row[i] for i in range(len(row)-1)]
ck('TI Newton coefficients nonnegative',all(d>=0 for d in D))
ck('TI Newton polynomial identity',all(b(r)==sum(D[j]*comb(r,j) for j in range(min(r,7)+1)) for r in range(16)))
print('VALUE TI Newton coefficients', D)
def zb(y): return sum(D[j]*(y/(1-y))**j for j in range(8))
E=Q(1,10**22); y=Q(1193,1250); kap=E*zb(y)*y**-150
ck('TI path kappa <= .0885',kap<=Q(885,10000))
ck('TI path kappa <= 1/2',kap<=Q(1,2))
val('TI kappa at 1e-22',kap)
y=Q(9322,10000); Z=zb(y); lam=E*Z*y**-100; p=E+E*Z*lam/(1-lam)
ck('TI sparse lambda <1',lam<1)
ck('TI p <= 2.4e-8',p<=Q(24,10**9))
ck('TI p <1/2',p<Q(1,2))
ck('TI old rate included',160000**101>=10**22)
val('TI lambda at 1e-22',lam); val('TI p at 1e-22',p)
print('TOTAL',checks,'exact checks passed.')

