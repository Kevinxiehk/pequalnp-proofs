# Explicit check of the hand-derived level N2 blocks with zero weights:
# (alpha2) columns: [sigma; sigma; sigma], three columns [x mu; u_t mu; v_t mu] (u,v in 1^perp, u.v = 0), fifth column [-3x mu; 0; 0].
# (alpha1) columns: [sigma;sigma;sigma] and four columns [X_c(t) mu; X_d(t) mu; X_e(t) mu], X_i in 1^perp pairwise orthogonal, sum X_c X_d X_e = 0.
import itertools, numpy as np
def perm(M):
    n=len(M); return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
rg=np.random.default_rng(0)
def defect(g,forms):
    w=0
    for _ in range(8):
        p=rg.normal(size=(3,2))+1j*rg.normal(size=(3,2)); p[2]=-p[0]-p[1]; t=np.zeros((5,5),complex)
        for i in range(3): t[2+i]=g[i]*(forms@p[i])
        w=max(w,abs(perm(np.ones((5,5))+t)-120))
    return w
sig=np.array([1,0]); mu=np.array([0,1]); x=0.7; u=np.array([1,2,-3.]); v=1.3*np.array([u[1]-u[2],u[2]-u[0],u[0]-u[1]])
g=np.array([[1,x,x,x,-3*x],[1,u[0],u[1],u[2],0],[1,v[0],v[1],v[2],0]],dtype=complex); forms=np.array([sig,mu,mu,mu,mu],dtype=complex)
print('(alpha2) level defect: %.2e'%defect(g,forms),'  (control with x -> 2x in the fifth column only: %.2e)'%defect(g*np.array([[1,1,1,1,2],[1]*5,[1]*5]),forms))
# alpha1: X_c, X_d, X_e in C^4, all orthogonal to 1 and pairwise orthogonal, triple sum zero: find by least squares
from scipy.optimize import least_squares
def res(z):
    X=(z[:12]+1j*z[12:]).reshape(3,4); r=[X[i].sum() for i in range(3)]+[X[0]@X[1],X[0]@X[2],X[1]@X[2],(X[0]*X[1]*X[2]).sum()]+[np.vdot(X[i],X[i])-1 for i in range(3)]
    r=np.array(r); return np.concatenate([r.real,r.imag,np.zeros(4)])
for k in range(20):
    s=least_squares(res,rg.normal(size=24),method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15)
    X=(s.x[:12]+1j*s.x[12:]).reshape(3,4)
    if np.linalg.norm(s.fun)<1e-12 and abs(X).min()>0.05: break
print('(alpha1) X found, residual %.1e, min |X| %.2f'%(np.linalg.norm(s.fun),abs(X).min()))
g=np.concatenate([np.ones((3,1)),X],axis=1); print('(alpha1) level defect: %.2e'%defect(g,forms))
