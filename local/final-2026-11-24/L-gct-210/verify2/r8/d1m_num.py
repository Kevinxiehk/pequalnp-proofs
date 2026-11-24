# verify2 r8: numerical cross-check of stage2 B-IND (R9-1) on the family FM with MY OWN T_1 code (cofactors by brute force).
# X (rows 0..4; row 0 = 0): rows 1,2 = s_1 e_0, s_2 e_0, rows 3,4 = p, q. B(ind): p_0 = -a-(1+mu)b, q_0 = (mu-1)a-b, s = (1-mu)a+(1+mu)b.
# FM: Y_0 coordinates (z1,z2,a,b): p' = z1(e1-e2) + ((a-2pi)/2,(a-2pi)/2,pi,pi), q' = z2(e3-e4) + (ka,ka,(b-2ka)/2,(b-2ka)/2),
#     pi = al a + be b, ka = ga a + de b with (be = ga = 0, 1 - al - de + 4 al de = 0) or (al = de = 1/4, be ga = -3/16).
# X = C xi_d + X_0, xi_d = (e_1 - e_2) e_0^T, X_0: s_1 = s_2 = s/2.  Check: level (perm = 120 at random points), dim T_1, dim Omega.
import numpy as np, itertools
rng=np.random.default_rng(11)
def perm(A):
    n=len(A); return sum(np.prod([A[i,s[i]] for i in range(n)]) for s in itertools.permutations(range(n)))
def cof(A):
    C=np.zeros((5,5),complex)
    for i in range(5):
        for j in range(5): C[i,j]=perm(np.delete(np.delete(A,i,0),j,1))
    return C
def member(comp):
    lam=rng.normal()+1j*rng.normal(); al=rng.normal()+1j*rng.normal(); ga=lam*(1-al)/(1-4*al)
    def lift(z1,z2,a):
        pp=np.array([(1-2*al)*a/2+z1,(1-2*al)*a/2-z1,al*a,al*a]); qq=np.array([ga*a,ga*a,(lam-2*ga)*a/2+z2,(lam-2*ga)*a/2-z2])
        q0=0; p0=-lam*q0-(1+lam)**2*a; s=(lam-1)*q0+lam*(1+lam)*a
        Y=np.zeros((5,5),complex); Y[1,0]=s/2; Y[2,0]=s/2; Y[3,0]=p0; Y[3,1:]=pp; Y[4,0]=q0; Y[4,1:]=qq; return Y
    xd=np.zeros((5,5),complex); xd[1,0]=1; xd[2,0]=-1
    k1=np.zeros((5,5),complex); k1[1,0]=(lam-1)/2; k1[2,0]=(lam-1)/2; k1[3,0]=-lam; k1[4,0]=1
    return [xd,k1,lift(1,0,0),lift(0,1,0),lift(0,0,1)]
for comp in (1,2):
    for trial in range(3):
        B=member(comp)
        lev=max(abs(perm(np.ones((5,5))+sum((rng.normal()+1j*rng.normal())*b for b in B))-120) for _ in range(5))
        rows=[]
        for _ in range(60):
            m=sum((rng.normal()+1j*rng.normal())*b for b in B); rows.append(cof(np.ones((5,5))+m).reshape(25))
        Mx=np.array(rows); u,sv,vh=np.linalg.svd(Mx); r=(sv>1e-9*sv[0]).sum(); T1=vh[r:].conj().T   # null space, conj-correct (bilinear)
        om=np.linalg.matrix_rank(T1.reshape(5,5,-1)[0,:,:],tol=1e-8)
        print('D1M comp %d trial %d: level err %.1e, dim T_1 = %d, dim Omega = %d'%(comp,trial,lev,T1.shape[1],om),flush=True)
