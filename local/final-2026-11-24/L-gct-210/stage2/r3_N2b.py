# Larger survey for the N2 block lemma: count solutions of (i)-(iii) that are zero-free (1e-3 < |a_j|,|b_j| < 1e3) and whose plane
# contains no unit vector (class structure not (4,1)); also a zero-avoiding parametrisation a = exp(al), b = exp(be).
import sys, numpy as np
from scipy.optimize import least_squares
ARGV=list(sys.argv); sys.argv=[sys.argv[0],sys.argv[1],'0']
import importlib.util
src=open('/home/kevxhk/work/L-gct-210/stage2/r3_N2.py').read().split("stats={}; ex={}")[0]
exec(src)
sys.argv=ARGV; rng=np.random.default_rng(int(sys.argv[1])); NT=int(sys.argv[3]) if len(sys.argv)>3 else 200
def unit_in_plane(lam,tol=1e-5):
    for j in range(5):
        M=np.delete(lam,j,axis=0)
        if np.linalg.svd(M,compute_uv=False)[-1]<tol: return True
    return False
def run(expo):
    st={'noconv':0,'zero_or_inf':0,'unit vector in P':0,'GENUINE':0}; best=None
    def res2(z):
        if expo:
            c=z[:22]+1j*z[22:]; zz=np.concatenate([c[:12],np.exp(c[12:])]); return res(np.concatenate([zz.real,zz.imag]))
        return res(z)
    for trial in range(NT):
        z=rng.normal(size=44)
        s=least_squares(res2,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
        if np.linalg.norm(s.fun)>1e-9: st['noconv']+=1; continue
        x=s.x
        if expo:
            c=x[:22]+1j*x[22:]; zz=np.concatenate([c[:12],np.exp(c[12:])]); x=np.concatenate([zz.real,zz.imag])
        lam,sig,a,b=unpack(x); m=min(abs(a).min(),abs(b).min()); M=max(abs(a).max(),abs(b).max())
        if m<1e-3 or M>1e3: st['zero_or_inf']+=1
        elif unit_in_plane(lam): st['unit vector in P']+=1
        else: st['GENUINE']+=1; best=(lam,sig,a,b)
    return st,best
for expo in ((False,) if len(sys.argv)>4 else (False,True)):
    st,best=run(expo); print('parametrisation','exp' if expo else 'plain',st,flush=True)
    if best is not None:
        np.set_printoptions(precision=5,suppress=True,linewidth=200); lam,sig,a,b=best
        print(' GENUINE example: lam=\n',lam,'\n sig=',sig,'\n a=',a,'\n b=',b,flush=True)
