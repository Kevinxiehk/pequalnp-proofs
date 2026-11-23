# Test of the k = 5 step of Lemma N2-GEN on the UNDERDETERMINED subsystem it uses (tau = 1):
#   sum nu = 0, sum nu z = 1;  sum b nu = 0, sum b nu z = 1;  sum a nu^2 z^r = (0,0,1);  sum b nu^2 z^r = (0,0,1);
#   sum a b nu^3 z^r = (0,0,0,1)        (14 equations, 20 unknowns nu,a,b,z in C^5).
# Claim: no solution with all nu_j, a_j, b_j != 0 and z_j pairwise distinct. LM from random starts; report the degeneracy of each solution.
import numpy as np
from scipy.optimize import least_squares
import sys; SYM=(len(sys.argv)>1); rg=np.random.default_rng(11)
def unpack(x): c=x[:20]+1j*x[20:]; return c[:5],c[5:10],c[10:15],c[15:20]
def res(x):
    nu,a,b,z=unpack(x); r=[nu.sum(),(nu*z).sum()-1,(b*nu).sum(),(b*nu*z).sum()-1]+([(a*nu).sum(),(a*nu*z).sum()-1] if SYM else [])
    for c in (a,b): r+=[(c*nu**2).sum(),(c*nu**2*z).sum(),(c*nu**2*z**2).sum()-1]
    W=a*b*nu**3; r+=[W.sum(),(W*z).sum(),(W*z**2).sum(),(W*z**3).sum()-1]
    r=np.array(r); return np.concatenate([r.real,r.imag,np.zeros(12 if not SYM else 8)])
st={'noconv':0,'degenerate':0,'GENUINE':0}; worst=0
for trial in range(120):
    x=rg.normal(size=40); s=least_squares(res,x,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=500)
    if np.linalg.norm(s.fun)>1e-10: st['noconv']+=1; continue
    nu,a,b,z=unpack(s.x); m=min(abs(nu).min(),abs(a).min(),abs(b).min()); dz=min(abs(z[i]-z[j]) for i in range(5) for j in range(i))
    big=max(abs(nu).max(),abs(a).max(),abs(b).max(),abs(z).max())
    q=min(m,dz,1/big); worst=max(worst,q)
    st['degenerate' if q<1e-4 else 'GENUINE']+=1
print(st,'  largest non-degeneracy measure min(|nu|,|a|,|b|,|z_i-z_j|,1/max) among solutions: %.2e'%worst)
