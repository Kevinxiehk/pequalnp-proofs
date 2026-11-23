# First-order extension test for N2 blocks: for a level 4-dim block X (rows c,d,e), T_1(X) := {t in C^{5x5} : sum t_ij perm_4((J+x)^(ij)) = 0
# for all x in X}; a level space containing X lies in T_1(X). Report dim T_1 for numerically found level blocks of each column type.
import sys, itertools, numpy as np
from scipy.optimize import least_squares
sys.argv=[sys.argv[0],sys.argv[1] if len(sys.argv)>1 else '5','0']
src=open('/home/claude/work/L-gct-210/stage2/r4_block.py').read().split("if __name__=='__main__':")[0]
exec(src)
P4=np.array(list(itertools.permutations(range(4))))
def cofs(M):                                  # M: (5,5) complex -> 25 cofactor permanents
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return out
def dimT1(F,npts=60):
    r2=np.random.default_rng(1); rows=[]
    for _ in range(npts):
        p=r2.normal(size=(3,2))+1j*r2.normal(size=(3,2)); p[2]=-p[0]-p[1]; M=np.ones((5,5),complex)
        for i in range(3): M[2+i]+=F[:,i,:]@p[i]
        rows.append(cofs(M))
    s=np.linalg.svd(np.array(rows),compute_uv=False); rk=int((s>1e-8*s[0]).sum()); return 25-rk, s[rk-1]/s[0]
res_count={}
for trial in range(int(sys.argv[1]) if False else 24):
    z=rg.normal(size=60); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
    if np.linalg.norm(s.fun)>1e-10: continue
    F=(s.x[:30]+1j*s.x[30:]).reshape(5,3,2); key=tuple(sorted(coltype(F[j]) for j in range(5))); d,sm=dimT1(F)
    res_count.setdefault((key,d),0); res_count[(key,d)]+=1
for (key,d),v in sorted(res_count.items(),key=lambda kv:-kv[1]): print(v,'blocks with column types',key,': dim T_1(X) =',d,flush=True)
