"""Exact checks for the classification of level spaces containing K.
(1) rank over C of first-order conditions at K is >= 15 (via reduction mod a prime p = 1 mod 15), so dim E(K) <= 10.
(2) Fourier forms of f_p(v) = sum_{j!=l} v_j v_l prod_{c not in {j,l}} p_c for p = chi1 + t chi4 and chi2 + t chi3,
    checked EXACTLY in Z[zeta15] (cyc.py class C) against the claimed integer coefficient forms."""
import sys, itertools, random
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
from cyc import C, ZERO, ONE, w5, z3
# ---------- (1) mod p ----------
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
p=10**9+1
while not (p%15==1 and isprime(p)): p+=1
# element of order 15
for a in range(2,1000):
    g=pow(a,(p-1)//15,p)
    if pow(g,5,p)!=1 and pow(g,3,p)!=1: break
W=lambda k: pow(g,3*k%15,p); Z=lambda k: pow(g,5*k%15,p)
u=[1,Z(2),Z(1),0,0]; ub=[1,Z(1),Z(2),0,0]
chi=lambda k:[W(k*j) for j in range(5)]
Kb=[[[u[i]*chi(1)[j]%p for j in range(5)] for i in range(5)],[[u[i]*chi(4)[j]%p for j in range(5)] for i in range(5)],
    [[ub[i]*chi(2)[j]%p for j in range(5)] for i in range(5)],[[ub[i]*chi(3)[j]%p for j in range(5)] for i in range(5)]]
def permp(M):
    k=len(M)
    if k==0: return 1
    tot=0
    for s in itertools.permutations(range(k)):
        pr=1
        for i in range(k): pr=pr*M[i][s[i]]%p
        tot+=pr
    return tot%p
def Pkp(T,k):
    m=len(T); n=len(T[0]); tot=0
    if k==0: return 1
    for R in itertools.combinations(range(m),k):
        for Cc in itertools.combinations(range(n),k):
            tot+=permp([[T[i][j] for j in Cc] for i in R])
    return tot%p
def gradp(T,k):
    out=[]
    for i in range(5):
        for j in range(5):
            sub=[[T[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]
            out.append(Pkp(sub,k-1))
    return out
def rankp(rows):
    A=[r[:] for r in rows]; r=0; ncol=len(A[0])
    for c in range(ncol):
        piv=next((i for i in range(r,len(A)) if A[i][c]%p),None)
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; inv=pow(A[r][c],p-2,p)
        A[r]=[x*inv%p for x in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]:
                f=A[i][c]; A[i]=[(x-f*y)%p for x,y in zip(A[i],A[r])]
        r+=1
    return r
random.seed(1); rows=[]
for s in range(8):
    a=[random.randrange(1,50) for _ in range(4)]   # integer combination -> point of K over Z[zeta15]
    T=[[sum(a[q]*Kb[q][i][j] for q in range(4))%p for j in range(5)] for i in range(5)]
    for k in range(1,6): rows.append(gradp(T,k))
print('p =',p,' rank of first-order system mod p:',rankp(rows),'(need 15 => dim E(K) <= 10)')
# ---------- (2) exact Fourier forms in Z[zeta15] ----------
def chiC(k): return [w5(k*j) for j in range(5)]
def fourier_form(pv):
    M=[[ZERO]*5 for _ in range(5)]
    for j in range(5):
        for l in range(5):
            if j!=l:
                pr=ONE
                for c in range(5):
                    if c not in (j,l): pr=pr*pv[c]
                M[j][l]=pr
    Ch=[chiC(a) for a in range(5)]   # Ch[a][j] = w^(aj)
    G=[[ZERO]*5 for _ in range(5)]
    for a in range(5):
        for b in range(5):
            tot=ZERO
            for j in range(5):
                for l in range(5):
                    if j!=l: tot=tot+Ch[a][j]*M[j][l]*Ch[b][l]
            G[a][b]=tot
    return G
# claimed: f_p = 2*sum_e t^e * (monomial coefficient dicts)
claims={(1,4):[{(0,2):-5,(1,1):10,(3,4):-5},{(0,4):10,(1,3):-15,(2,2):5},{(0,1):10,(2,4):-15,(3,3):5},{(0,3):-5,(1,2):-5,(4,4):10}],
        (2,3):[{(0,4):-5,(1,3):-5,(2,2):10},{(0,3):10,(1,2):-15,(4,4):5},{(0,2):10,(1,1):5,(3,4):-15},{(0,1):-5,(2,4):-5,(3,3):10}]}
ok=True
for (a,b),cl in claims.items():
    for t in range(4):
        pv=[w5(a*j)+w5(b*j)*t for j in range(5)]
        G=fourier_form(pv)
        for x in range(5):
            for y in range(5):
                # claimed G_xy: diagonal = 2*coeff, offdiag = coeff (since 2*coeff/2)
                key=(min(x,y),max(x,y)); val=sum(2*cl[e].get(key,0)*t**e for e in range(4))
                if x!=y: val=val//2 if False else val  # coefficient of nu_x nu_y in f is 2*G_xy -> G_xy = val/2
                target = val if x==y else None
                if x==y: diff=G[x][y]-C([val])
                else: diff=G[x][y]*2-C([val])
                if not diff.iszero(): ok=False; print('MISMATCH',(a,b),t,x,y,G[x][y],val)
print('exact Fourier forms verified:',ok)
