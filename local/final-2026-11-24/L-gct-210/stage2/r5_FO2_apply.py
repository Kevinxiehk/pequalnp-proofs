# Apply (FO2) to: level N2 blocks X_ab found by LM (generic and diagonal), M*, and the saved candidates for L_r.
import sys, glob, itertools, numpy as np
from scipy.optimize import least_squares
from collections import Counter
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rgm=np.random.default_rng(5)
# --- M* ---
def rowvec(i,v):
    M=np.zeros((5,5)); M[i]=v; return M
def E(i,j,v=1):
    M=np.zeros((5,5)); M[i,j]=v; return M
def Mstar(ma,mb,al,be,ga):
    a,b,c,d,e=0,1,2,3,4; Xc=np.array([0,al,0,0,-al.real if False else -al]); Xd=np.array([0,be,-be,-be,be]); Xe=np.array([0,0,ga,-ga,0])
    return [rowvec(a,[-1,0,0,0,0])+rowvec(c,[1,ma*al,0,0,-ma*al]), rowvec(b,[-1,0,0,0,0])+rowvec(c,[1,mb*al,0,0,-mb*al]),
            E(c,0)-E(d,0), E(c,0)-E(e,0), rowvec(c,Xc)-rowvec(d,Xd), rowvec(c,Xc)-rowvec(e,Xe)]
for par in ((1,2,1,1,1),(0,0,1,1,1),(2,5,3,-2,7)):
    n,rho,bd=FO2(Mstar(*[float(x) for x in par]),rgm); print('M*',par,': dim T_1 = %d, rank q_m = %d, bound on dim L = %d'%(n,rho,bd),flush=True)
# --- saved L_r candidates ---
for f in sorted(glob.glob('/tmp/r5_Lr3_*.npy')+glob.glob('/tmp/r5_Lr_*.npy')):
    B=np.load(f); X=np.zeros((5,5,5),complex); X[:,1:,:]=B
    n,rho,bd=FO2(X,rgm); print('L_r candidate',f.split('/')[-1],': dim T_1 = %d, rank q_m = %d, bound on dim L = %d'%(n,rho,bd),flush=True)
# --- N2 blocks ---
if len(A)>1:
    sys.argv=[A[0],A[1],'0']
    exec(open('/home/kevxhk/work/L-gct-210/stage2/r4_block.py').read().split("if __name__=='__main__':")[0])
    cnt=Counter()
    for trial in range(int(A[2]) if len(A)>2 else 12):
        z=rg.normal(size=60); s=least_squares(res,z,method='lm',xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
        if np.linalg.norm(s.fun)>1e-10: continue
        F=(s.x[:30]+1j*s.x[30:]).reshape(5,3,2); Xb=np.zeros((4,5,5),complex)
        Xb[:,2:,:]=elems(F,np.eye(4,dtype=complex)); n,rho,bd=FO2(Xb,rgm)
        cnt[(tuple(sorted(coltype(F[j]) for j in range(5))),'dim T_1',n,'rank q_m',rho,'bound',bd)]+=1
    for k,v in cnt.items(): print('N2 block:',v,k,flush=True)
