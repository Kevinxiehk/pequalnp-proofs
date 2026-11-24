# verify2 r13: check rows R11.5/R11.6 (generic two-column (2,1) stratum): with z_c, z_d, z_e = (m_t/4) 1, l == 0, the deletion vector of t Z is
# C_a = 6 x_c x_d x_e (4 + t m_b) - 24, C_b = 6 x_c x_d x_e (4 + t m_a) - 24, C_c = 2 x_d x_e (12 + 3t(m_a+m_b) + t^2 (m_a m_b - q)) - 24, ...
# (x_k = 1 + t m_k/4).  (i) first verify these closed forms against a direct permanent on random data; (ii) Groebner: (C_j - 24) = lam(t) m_j for all t,
# sum m = 0, m_a = 1, u m_b m_c m_d m_e = 1  -> claim: UNIT (some entry of m vanishes).
import sympy as sp, itertools, random
t,q=sp.symbols('t q'); ma,mb,mc,md,me=sp.symbols('ma mb mc md me')
x=lambda mk: 1+t*mk/4
def closed(m,q):
    ma_,mb_,mc_,md_,me_=m
    Ca=6*x(mc_)*x(md_)*x(me_)*(4+t*mb_)-24; Cb=6*x(mc_)*x(md_)*x(me_)*(4+t*ma_)-24
    Cc=2*x(md_)*x(me_)*(12+3*t*(ma_+mb_)+t**2*(ma_*mb_-q))-24
    Cd=2*x(mc_)*x(me_)*(12+3*t*(ma_+mb_)+t**2*(ma_*mb_-q))-24
    Ce=2*x(mc_)*x(md_)*(12+3*t*(ma_+mb_)+t**2*(ma_*mb_-q))-24
    return [Ca,Cb,Cc,Cd,Ce]
# (i) direct check: random z_a, z_b with column sums m_a, m_b; z_t = (m_t/4) 1
random.seed(1)
m=[sp.Rational(random.randint(-5,5),random.randint(1,3)) for _ in range(4)]; m.append(-sum(m))
za=[sp.Rational(random.randint(-5,5),2) for _ in range(3)]; za.append(m[0]-sum(za))
zb=[sp.Rational(random.randint(-5,5),2) for _ in range(3)]; zb.append(m[1]-sum(zb))
Z=[[za[r],zb[r]]+[m[k]/4 for k in (2,3,4)] for r in range(4)]
qv=sum(za[r]*zb[r] for r in range(4))
def perm(M):
    return sp.expand(sum(sp.prod([M[r][p[r]] for r in range(4)]) for p in itertools.permutations(range(4))))
direct=[sp.expand(perm([[1+t*Z[r][c] for c in range(5) if c!=j] for r in range(4)])-24) for j in range(5)]
cf=[sp.expand(e) for e in closed(m,qv)]
print('closed forms agree with direct permanents:',all(sp.expand(a-b)==0 for a,b in zip(direct,cf)))
# (ii) Groebner
lam=sp.symbols('l1:5'); L=sum(lam[k]*t**(k+1) for k in range(4))
C=closed([ma,mb,mc,md,me],q); mm=[ma,mb,mc,md,me]
eqs=[]
for j in range(5):
    eqs+=sp.Poly(sp.expand(C[j]-L*mm[j]),t).all_coeffs()
u=sp.Symbol('u')
eqs+= [ma+mb+mc+md+me, ma-1, u*mb*mc*md*me-1]
G=sp.groebner([e for e in eqs if e!=0],*(list(lam)+[q,u,ma,mb,mc,md,me]),order='grevlex')
print('all entries nonzero (chart m_a = 1): Groebner basis =',G.exprs[:3], '... UNIT' if G.exprs==[1] else '')
# calibration: drop the Rabinowitsch -> solutions should exist (with a zero entry)
G2=sp.groebner([e for e in eqs[:-1] if e!=0],*(list(lam)+[q,ma,mb,mc,md,me]),order='grevlex')
print('calibration (zero entries allowed): unit?',G2.exprs==[1])
