# Type IV: five isotropic columns v(theta_m), N = ker[1;theta;theta^2] (2-dim); conditions perm of each 4-subset = 0 and cubic C3_m on N
import numpy as np, itertools
from scipy.optimize import least_squares
I=1j; chi=lambda a: np.array([I**(a*j) for j in range(4)])
def v(t): return chi(1)+t*chi(2)-t*t/2*chi(3)
def perm(M): return sum(np.prod([M[s[j],j] for j in range(4)]) for s in itertools.permutations(range(4)))
rng=np.random.default_rng(int(__import__("sys").argv[2]) if len(__import__("sys").argv)>2 else 0)
# verify closed formula perm = 2 e2^2 - 1.5 (e4-4)^2
t=rng.normal(size=4)+1j*rng.normal(size=4)
e=lambda k: sum(np.prod(c) for c in itertools.combinations(t,k))
print('formula check',abs(perm(np.column_stack([v(x) for x in t]))-(2*e(2)**2-1.5*(e(4)-4)**2)))
def cfun(a,b): return 2*b+a+a*b**4/4+a*a*b**3/2
print('c check',abs(4*cfun(t[0],t[1])-(v(t[0])*v(t[1])**2).sum()))
def resid(th):
    out=[]
    for m in range(5):
        tt=np.delete(th,m); ee=lambda k: sum(np.prod(c) for c in itertools.combinations(tt,k))
        out.append(2*ee(2)**2-1.5*(ee(4)-4)**2)
    A=np.vstack([np.ones(5),th,th**2])
    u,s,vh=np.linalg.svd(A); Nb=vh[3:].conj().T  # 5x2 basis of kernel (if rank 3)
    for m in range(5):
        kap=np.array([cfun(th[m],th[a]) for a in range(5)]); kap[m]=-cfun(th[m],th[m])
        G=Nb.T@np.diag(kap)@Nb; out+=[G[0,0],G[0,1],G[1,1]]
    return np.array(out)
def res(x): r=resid(x[:5]+1j*x[5:]); return np.concatenate([r.real,r.imag])
sols=[]
for tr in range(int(__import__("sys").argv[1])):
    x0=rng.normal(size=10)*float(__import__("sys").argv[3]) if len(__import__("sys").argv)>3 else rng.normal(size=10)*1.5
    sol=least_squares(res,x0,method='lm',max_nfev=600,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    th=sol.x[:5]+1j*sol.x[5:]
    print("tr",tr,"cost %.2e"%sol.cost,np.round(th,3),flush=True)
    if sol.cost<1e-20:
        d=sorted(abs(th[a]-th[b]) for a in range(5) for b in range(a))
        sols.append((sol.cost,np.round(th,4),d[0]))
print("converged:",len(sols))
for s in sols[:12]: print('cost %.1e'%s[0],s[1],'min gap %.2e'%s[2])
