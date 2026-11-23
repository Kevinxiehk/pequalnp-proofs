# Family (alpha) inside N2: Xi = [X_c;X_d;X_e] (3x4), X_i orthogonal to 1, pairwise orthogonal, sum X_c X_d X_e = 0.
# (Z2) on L_a = X_ab + C x^{bc}, rho_b = rho_1 e_{j1} + rho', gives
#   (E0) perm_4[rho';X_c;X_d;X_e] = 0; (E1) all 3x3 subpermanents of [rho';X_i;X_k] vanish (three pairs); (E2) rho_1 * (3x3 subperms of Xi) = 0.
# Case A (rho_1 != 0): all four 3x3 subpermanents of Xi vanish.   Case B (rho_1 = 0): rho' != 0 with (E0), (E1).
import sys, itertools, numpy as np
from scipy.optimize import least_squares
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def perm(M):
    n=len(M); return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
def base(X):
    return [X[i].sum() for i in range(3)]+[X[0]@X[1],X[0]@X[2],X[1]@X[2],(X[0]*X[1]*X[2]).sum()]+[np.vdot(X[i],X[i])-1 for i in range(3)]
def resA(z):
    X=(z[:12]+1j*z[12:]).reshape(3,4); r=base(X)+[perm(np.delete(X,j,axis=1)) for j in range(4)]
    r=np.array(r); return np.concatenate([r.real,r.imag])
def resB(z):
    c=z[:16]+1j*z[16:]; X=c[:12].reshape(3,4); rho=c[12:]; r=base(X)+[np.vdot(rho,rho)-1,perm(np.vstack([rho,X]))]
    for i,k in ((0,1),(0,2),(1,2)): r+=[perm(np.delete(np.vstack([rho,X[i],X[k]]),j,axis=1)) for j in range(4)]
    r=np.array(r); return np.concatenate([r.real,r.imag])
for name,res,n in (('A',resA,24),('B',resB,32)):
    st={'noconv':0,'sol':0}; mins=[]
    for trial in range(60):
        z=rg.normal(size=n); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400) if len(res(z))>=n else least_squares(res,z,xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400)
        if np.linalg.norm(s.fun)>1e-10: st['noconv']+=1; continue
        X=(s.x[:n//2][:12]+1j*s.x[n//2:][:12]).reshape(3,4); st['sol']+=1
        zero_cols=[t for t in range(4) if np.linalg.norm(X[:,t])<1e-6]; nz=int((abs(X)<1e-6).sum()); rk=np.linalg.matrix_rank(X,tol=1e-6)
        mins.append((nz,tuple(zero_cols),rk))
    from collections import Counter
    print('case',name,st,' (number of zero entries of Xi, zero columns, rank Xi) -> count:',dict(Counter(mins)),flush=True)
