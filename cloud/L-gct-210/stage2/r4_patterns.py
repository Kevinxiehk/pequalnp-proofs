# Pattern-constrained survey of the diagonal model with zero weights: t_ij = g_ij lam_j(p_i), g_ij != 0 exactly on a prescribed support
# pattern (g = exp(x) there), level conditions (i),(ii),(iii).  For every pattern (up to permuting rows c,d,e and columns) with >= 2
# columns in each row: LM from a few starts; a solution counts if all three row maps are injective (smin > 1e-3) and all prescribed
# forms are nonzero (norm > 1e-3).  Output per pattern: number of genuine solutions and the dims of single-column elements found.
import sys, itertools, warnings, numpy as np
warnings.filterwarnings('ignore')
from scipy.optimize import least_squares
A=sys.argv; SEED=int(A[1]); LO=int(A[2]); HI=int(A[3]); NS=int(A[4]) if len(A)>4 else 2
rg=np.random.default_rng(SEED)
types=[tuple(int(b) for b in f'{k:03b}') for k in range(8)]
def canon(cols):
    best=None
    for rp in itertools.permutations(range(3)):
        c=tuple(sorted(tuple(col[rp[i]] for i in range(3)) for col in cols))
        if best is None or c<best: best=c
    return best
pats=sorted({canon(c) for c in itertools.combinations_with_replacement(types,5) if all(sum(col[i] for col in c)>=2 for i in range(3))})
if len(A)>5 and A[5]=='two': pats=[q for q in pats if any(sum(c)==2 for c in q)]      # only patterns with a two-row column
if len(A)>5 and A[5]=='no2': pats=[q for q in pats if not any(sum(c)==2 for c in q)]   # only patterns with 3/1/0-weight columns (Lemma N2-Z)
def sq(l): return np.array([l[0]**2,2*l[0]*l[1],l[1]**2])
def cu(l): return np.array([l[0]**3,3*l[0]**2*l[1],3*l[0]*l[1]**2,l[1]**3])
def rk(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
def run(pat):
    S=np.array(pat).T                      # 3 x 5
    idx=[(i,j) for i in range(3) for j in range(5) if S[i,j]]; nz=[j for j in range(5) if S[:,j].any()]
    first={j:min(i for i in range(3) if S[i,j]) for j in nz}; free=[(i,j) for (i,j) in idx if first[j]!=i]      # gauge: first weight of each column = 1
    nw=len(free); nl=len(nz); n=nw+2*nl+2
    def unpack(z):
        c=z[:n]+1j*z[n:]; g=np.zeros((3,5),complex)
        for j in nz: g[first[j],j]=1
        for k,(i,j) in enumerate(free): g[i,j]=np.exp(c[k])
        lam=np.zeros((5,2),complex); lam[nz]=c[nw:nw+2*nl].reshape(nl,2); return g,lam,c[nw+2*nl:]
    def res(z):
        g,lam,sig=unpack(z); r=[g[i]@lam-sig for i in range(3)]
        L2=np.array([sq(l) for l in lam]); L3=np.array([cu(l) for l in lam])
        for i,k in ((0,1),(0,2),(1,2)): r.append((g[i]*g[k])@L2-sq(sig))
        r.append((g[0]*g[1]*g[2])@L3-cu(sig)); r=np.concatenate(r); G=lam.conj().T@lam
        out=np.concatenate([r.real,r.imag,[G[0,0].real-1,G[1,1].real-1,G[0,1].real,G[0,1].imag]])
        return np.concatenate([out,np.zeros(max(0,2*n-len(out)))])
    good=0; zcs=set()
    for st in range(NS):
        z=rg.normal(size=2*n)*0.7; s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=150)
        if np.linalg.norm(s.fun)>1e-9: continue
        g,lam,sig=unpack(s.x); forms=np.array([[g[i,j]*lam[j] for j in range(5)] for i in range(3)])     # 3,5,2
        if min(np.linalg.svd(forms[i],compute_uv=False)[-1] for i in range(3))<1e-3: continue
        if min(np.linalg.norm(forms[i,j]) for (i,j) in idx)<1e-3: continue
        B=[]
        for k in range(4):
            pts=np.zeros(4,complex); pts[k]=1; p=[pts[:2],pts[2:],-pts[:2]-pts[2:]]
            B.append(np.array([forms[i]@p[i] for i in range(3)]))
        B=np.array(B); good+=1; zcs.add(tuple(4-rk(np.delete(B,j,axis=2).reshape(4,-1)) for j in range(5)))
    return good,zcs
if __name__=='__main__':
    print('number of patterns:',len(pats),flush=True)
    for k,pat in enumerate(pats[LO:HI]):
        good,zcs=run(pat)
        if good: print(LO+k,' '.join(''.join(map(str,c)) for c in pat),' genuine solutions:',good,' single-column dims per column:',sorted(zcs),flush=True)
    print('done',LO,HI,flush=True)
