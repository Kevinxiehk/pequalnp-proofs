# Case N2 (stage3 sec.16) in GEN.  X_ab = {(g_c o pi_c; g_d o pi_d; g_e o pi_e): pi_i in P^, sum pi_i = 0}, g = 1/K' (zero-free).
# Level conditions on X_ab alone (P_1,P_2,P_3), with lam_j = j-th coordinate on P^ (binary linear forms), sigma a linear form:
#   (i) sum_j g_ij lam_j = sigma   (ii) sum_j g_ij g_kj lam_j^2 = sigma^2   (iii) sum_j g_cj g_dj g_ej lam_j^3 = sigma^3.
# Normalise g_c = 1, a = g_d, b = g_e.  LM search; classify solutions (zeros of a,b; proportionality classes of the lam_j).
import sys, numpy as np
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def unpack(z):
    c=z[:22]+1j*z[22:]; return c[:10].reshape(5,2), c[10:12], c[12:17], c[17:22]
def sq(l): return np.array([l[0]**2,2*l[0]*l[1],l[1]**2])
def cu(l): return np.array([l[0]**3,3*l[0]**2*l[1],3*l[0]*l[1]**2,l[1]**3])
def res(z):
    lam,sig,a,b=unpack(z); r=[]
    for c in (np.ones(5),a,b): r.append(c@lam-sig)
    L2=np.array([sq(l) for l in lam]); L3=np.array([cu(l) for l in lam])
    for c in (a,b,a*b): r.append(c@L2-sq(sig))
    r.append((a*b)@L3-cu(sig))
    r=np.concatenate(r); G=lam.conj().T@lam
    return np.concatenate([r.real,r.imag,[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag,0,0]])
def classes(lam,tol=1e-6):
    cl=[]; 
    for j in range(5):
        if np.linalg.norm(lam[j])<tol: cl.append('0'); continue
        for k,(rep,name) in enumerate(reps):
            if abs(lam[j][0]*rep[1]-lam[j][1]*rep[0])<tol*10: cl.append(name); break
        else: reps.append((lam[j],chr(65+len(reps)))); cl.append(reps[-1][1])
    return ''.join(cl)
stats={}; ex={}
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 40):
    z=rng.normal(size=44)
    s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=400)
    if np.linalg.norm(s.fun)>1e-9: stats['noconv']=stats.get('noconv',0)+1; continue
    lam,sig,a,b=unpack(s.x); reps=[]; cl=classes(lam)
    # canonical relabel of class pattern
    za=''.join('z' if abs(x)<1e-6 else ('I' if abs(x)>1e6 else '.') for x in a); zb=''.join('z' if abs(x)<1e-6 else ('I' if abs(x)>1e6 else '.') for x in b)
    key=(tuple(sorted(cl.count(ch) for ch in set(cl)-{'0'}))[::-1], cl.count('0'), 'zerofree' if ('z' not in za+zb and 'I' not in za+zb) else 'HASZERO', 'sig0' if np.linalg.norm(sig)<1e-6 else 'sig')
    stats[key]=stats.get(key,0)+1; ex.setdefault(key,(cl,lam,sig,a,b))
for k,v in sorted(stats.items(),key=lambda kv:-kv[1] if kv[0]!='noconv' else 0): print(k,v)
np.set_printoptions(precision=4,suppress=True,linewidth=200)
for k,(cl,lam,sig,a,b) in ex.items():
    if k[2]=='zerofree':
        print('--- zero-free example',k,cl); print(' lam=',lam.tolist() if False else np.round(lam,4).tolist()); print(' sig=',np.round(sig,4),'\n a=',np.round(a,4),'\n b=',np.round(b,4))
