# verify2: structural claims about the annihilators in N2-X (beta-1): generators of K, exact.
import itertools, random
from fractions import Fraction as Fr
src=open('/home/claude/work/L-gct-210/verify2/n2x_annihilators.py').read().split("rnd=random.Random(7)")[0]
exec(src)
rnd=random.Random(11); R=lambda: Fr(rnd.choice([-5,-4,-3,-2,-1,1,2,3,4,5]),rnd.choice([1,1,2,3]))
vec=lambda d:[Fr(d.get(j,0)) for j in range(5)]
def nullvec(rows,n=10):
    # exact nullspace basis
    M=[list(r) for r in rows]; piv=[]; r=0
    for c in range(n):
        p=next((i for i in range(r,len(M)) if M[i][c]!=0),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==len(M): break
    out=[]
    for f in [c for c in range(n) if c not in piv]:
        v=[Fr(0)]*n; v[f]=Fr(1)
        for i,c in enumerate(piv): v[c]=-M[i][f]
        out.append(v)
    return out
def Lam(u,beta,B):
    # {l in C^B : M_u l in C beta}, M_u[z,z'] = u_{third}
    z=B; M=[[Fr(0)]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            if i!=j: M[i][j]=u[z[3-i-j]]
    # unknowns l (3), c (1): M l - c beta = 0
    rows=[[M[i][0],M[i][1],M[i][2],-beta[z[i]]] for i in range(3)]
    ns=nullvec(rows,4); return [[Fr(0)]*z[0]+[] for _ in ()] or [vec({z[0]:v[0],z[1]:v[1],z[2]:v[2]}) for v in ns]
ok=True; terms=set()
for trial in range(40):
    a0,a1,b2,b3,b4=R(),R(),R(),R(),R(); beta=vec({2:b2,3:b3,4:b4})
    h=vec({0:a1,1:-a0}); hs=vec({0:a1,1:a0}); u0=vec({2:b3,3:-b2}); u1=vec({3:b4,4:-b3}); V3=[h,u0,u1]
    # (2,3), P = C u + C h with u generic in V_B, and with u having a zero entry
    for u in ((lambda p,q:[p*x+q*y for x,y in zip(u0,u1)])(R(),R()),u0,u1,vec({2:b4,4:-b2})):
        S2=PV([u,h],V3); K=nullvec(cond_rows(S2)); L=Lam(u,beta,(2,3,4))
        if len(K)!=1 or len(L)!=1 or not inK(prod2(hs,L[0]),S2): ok=False
        terms.add(sum(1 for x in K[0] if x!=0))
    # (1,3): alpha = e_0, B = {1,2,3}, x = 4, P = C e_x + C u_0
    c1,c2,c3=R(),R(),R(); bt=vec({1:c1,2:c2,3:c3}); v0=vec({1:c2,2:-c1}); v1=vec({2:c3,3:-c2}); e4=vec({4:1}); V3=[v0,v1,e4]
    Qb=[Fr(0)]*10; Qb[pi[(2,3)]]=c1; Qb[pi[(1,3)]]=c2; Qb[pi[(1,2)]]=c3
    for u in ((lambda p,q:[p*x+q*y for x,y in zip(v0,v1)])(R(),R()),v0,v1):
        S2=PV([e4,u],V3); K=nullvec(cond_rows(S2)); L=Lam(u,bt,(1,2,3))
        if len(K)!=2 or len(L)!=1 or not inK(Qb,S2) or not inK(prod2(e4,L[0]),S2): ok=False
print('40 random parameter sets: (2,3) P = Cu + Ch: K = C H* L_0 with Lam(u) = C l_0 (also for u with a zero entry);')
print('                          (1,3) P = Ce_x + Cu_0: K = C Q_beta + y_x Lam(u_0), dim 2:   all claims hold:',ok)
print('number of nonzero coefficients of the generator of K in the (2,3) case:',sorted(terms),'(a monomial would have 1)')
