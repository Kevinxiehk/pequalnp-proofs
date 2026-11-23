# Direct test of the derivation (Z2) => (E0),(E1),(E2) in family (alpha):
# L_a = {(s rho_b; y_c e_0 + s_c X_c; y_d e_0 + s_d X_d; y_e e_0 + s_e X_e) : sum y_i = s w_sigma, sum s_i = s w_mu}  (X_i on columns 1..4),
# conditions: X_i orthogonal to 1, pairwise orthogonal, sum X_c X_d X_e = 0, and ALL 4x4 subpermanents of these 4x5 matrices vanish
# (evaluated directly at random points). LM; report for each solution: zeros per column of Xi, |rho'|, |rho_1|.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
from collections import Counter
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
P4=np.array(list(itertools.permutations(range(4))))
def perm4(A): return A[:,np.arange(4)[None,:],P4].prod(axis=2).sum(axis=1)
PTS=rg.normal(size=(14,5))+1j*rg.normal(size=(14,5))          # s, y_c, y_d, s_c, s_d
def unpack(z): c=z[:19]+1j*z[19:]; return c[:12].reshape(3,4),c[12:17],c[17],c[18]
def res(z):
    X,rho,ws,wm=unpack(z); s=PTS[:,0]; yc=PTS[:,1]; yd=PTS[:,2]; sc=PTS[:,3]; sd=PTS[:,4]; ye=s*ws-yc-yd; se=s*wm-sc-sd
    M=np.zeros((14,4,5),complex); M[:,0,:]=s[:,None]*rho
    for k,(y,si) in enumerate(((yc,sc),(yd,sd),(ye,se))): M[:,k+1,0]=y; M[:,k+1,1:]=si[:,None]*X[k]
    r=[perm4(np.delete(M,j,axis=2)) for j in range(5)]
    r=np.concatenate(r+[np.array([X[i].sum() for i in range(3)]+[X[0]@X[1],X[0]@X[2],X[1]@X[2],(X[0]*X[1]*X[2]).sum()])])
    nr=[np.vdot(X[i],X[i]).real-1 for i in range(3)]+[np.vdot(rho,rho).real-1]
    return np.concatenate([r.real,r.imag,nr])
st=Counter()
for trial in range(40):
    z=rg.normal(size=38); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=300)
    if np.linalg.norm(s.fun)>1e-9: st['no convergence']+=1; continue
    X,rho,ws,wm=unpack(s.x); zc=tuple(int((abs(X[:,t])<1e-6).sum()) for t in range(4))
    st[('zeros per column of Xi:',tuple(sorted(zc)),'rho_prime = 0:',bool(np.linalg.norm(rho[1:])<1e-6),'rho_1 != 0:',bool(abs(rho[0])>1e-6))]+=1
for k,v in st.items(): print(v,k)
