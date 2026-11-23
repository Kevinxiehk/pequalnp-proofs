# Diagonal model with weights allowed to vanish: X = {(g_c o lam(p_c); g_d o lam(p_d); g_e o lam(p_e)) : sum p_i = 0}, t_ij = g_ij lam_j(p_i),
# g in C^{3x5} (zeros allowed), lam_j binary linear forms (|lam_j| = 1 gauge), sigma a form.  Level conditions:
#   (i) sum_j g_ij lam_j = sigma, (ii) sum_j g_ij g_kj lam_j^2 = sigma^2, (iii) sum_j g_cj g_dj g_ej lam_j^3 = sigma^3.
# LM survey; classify solutions by the zero pattern of g (canonical under row/column permutations), injectivity of the three row maps,
# proportionality classes of the lam_j, and the dimension of the space of single-column elements.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); from pairlib import rank
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1); NT=int(sys.argv[2]) if len(sys.argv)>2 else 100
def unpack(z): c=z[:27]+1j*z[27:]; return c[:15].reshape(3,5),c[15:25].reshape(5,2),c[25:27]
def sq(l): return np.array([l[0]**2,2*l[0]*l[1],l[1]**2])
def cu(l): return np.array([l[0]**3,3*l[0]**2*l[1],3*l[0]*l[1]**2,l[1]**3])
def res(z):
    g,lam,sig=unpack(z); r=[g[i]@lam-sig for i in range(3)]
    L2=np.array([sq(l) for l in lam]); L3=np.array([cu(l) for l in lam])
    for i,k in ((0,1),(0,2),(1,2)): r.append((g[i]*g[k])@L2-sq(sig))
    r.append((g[0]*g[1]*g[2])@L3-cu(sig)); r=np.concatenate(r)
    G=lam.conj().T@lam; nr=[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag]
    return np.concatenate([r.real,r.imag,nr,np.zeros(12)])
def canon(pat):
    best=None
    for rp in itertools.permutations(range(3)):
        cols=sorted(tuple(pat[rp[i]][j] for i in range(3)) for j in range(5))
        if best is None or cols<best: best=cols
    return tuple(best)
def analyse(z,tol=1e-5):
    g,lam,sig=unpack(z); pat=[[int(abs(g[i,j])*np.linalg.norm(lam[j])>tol) for j in range(5)] for i in range(3)]
    inj=[np.linalg.svd(np.array([g[i,j]*lam[j] for j in range(5)]),compute_uv=False)[-1]>1e-4 for i in range(3)]
    B=[]
    for k in range(4):
        pts=np.zeros(4,complex); pts[k]=1; p=[pts[:2],pts[2:],-pts[:2]-pts[2:]]
        B.append(np.array([[g[i,j]*(lam[j]@p[i]) for j in range(5)] for i in range(3)]))
    B=np.array(B); zc=sum(4-rank(np.delete(B,j,axis=2).reshape(4,-1)) for j in range(5)) if rank(B.reshape(4,-1))==4 else -1
    return canon(pat),all(inj),zc,rank(B.reshape(4,-1)),np.linalg.norm(sig)>tol
if __name__=='__main__':
    stats={}
    for trial in range(NT):
        z=rg.normal(size=54); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=300)
        if np.linalg.norm(s.fun)>1e-9: stats['noconv']=stats.get('noconv',0)+1; continue
        key=analyse(s.x); stats[key]=stats.get(key,0)+1
        if key[1]: np.save('/tmp/r4_w_inj_%d.npy'%trial,s.x)
    print('columns of the pattern = supports (rows c,d,e) of the five columns; then: all row maps injective, total dim of single-column elements, dim X, sigma != 0')
    for k,v in sorted(stats.items(),key=lambda kv:(-kv[1] if kv[0]!='noconv' else 1)):
        if k=='noconv': print(v,'no convergence'); continue
        print(v,' '.join(''.join(map(str,c)) for c in k[0]),' injective:',k[1],' single-col dim:',k[2],' dimX:',k[3],' sigma!=0:',k[4])
