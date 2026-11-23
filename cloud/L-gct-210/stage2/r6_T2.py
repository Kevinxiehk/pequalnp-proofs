# Second necessary condition from chief's identity (**) at v -> 0 (row r of u = v, the other rows = T(v) + xi, xi in L_r):
#   <v, G(T(v) + xi)> = 120 <kappa,v>^5.   Order 1 in v: G(xi) = 0  [(ii)].   Order 2 in v:
#   (T2)  D_{T_k} G_j(xi) + D_{T_j} G_k(xi) = 0  for all j <= k and all xi in L_r,   T_k := T(e_k) in C^{4x5},  sum_k T_k = J' mod L_r.
# (T2) is LINEAR in T. For a candidate X = L_r: solve it, and test whether some solution has sum_k T_k = J' modulo X.
import sys, glob, itertools, numpy as np
P3=np.array(list(itertools.permutations(range(3))))
def perm3(M): return M[np.arange(3)[None,:],P3].prod(axis=1).sum()
def DG(xi):
    # D[j][i,l] = d G_j / d xi_{il} = perm_3(xi without row i, without columns j,l)  (0 if l == j)
    D=np.zeros((5,4,5),complex)
    for j in range(5):
        for i in range(4):
            rows=[a for a in range(4) if a!=i]
            for l in range(5):
                if l==j: continue
                cols=[c for c in range(5) if c not in (j,l)]; D[j,i,l]=perm3(xi[np.ix_(rows,cols)])
    return D
def T2test(B,rg,npts=30):
    eqs=[]
    for _ in range(npts):
        xi=np.tensordot(rg.normal(size=5)+1j*rg.normal(size=5),B,axes=1); D=DG(xi)
        for j in range(5):
            for k in range(j,5):
                row=np.zeros((5,4,5),complex); row[k]+=D[j]; row[j]+=D[k]; eqs.append(row.ravel())       # unknown T[k,i,l]
    A=np.array(eqs); u,s,vh=np.linalg.svd(A,full_matrices=True); r=int((s>1e-9*s[0]).sum()); ns=vh[r:].conj()          # solutions T (flattened 100)
    # image of T -> sum_k T_k (20-vector); is J' in image + X ?
    S=np.array([t.reshape(5,20).sum(axis=0) for t in ns]).T                                # 20 x dim
    M=np.concatenate([S,B.reshape(5,20).T],axis=1); c,_,_,_=np.linalg.lstsq(M,np.ones(20,dtype=complex),rcond=None); err=np.linalg.norm(M@c-np.ones(20))
    return len(ns),err
if __name__=='__main__':
    rg=np.random.default_rng(3)
    files=sorted(glob.glob('/tmp/r5_Lr3_1_[12].npy')+glob.glob('/tmp/r6_census_*.npy')+glob.glob('/tmp/r6_fk_*.npy'))
    for f in files:
        B=np.load(f); n,err=T2test(B,rg); print('%-26s dim of the solution space of (T2) = %3d (25 = only T_k in L_r);  distance of J\' from {sum_k T_k} + L_r: %.2e'%(f.split('/')[-1],n,err),flush=True)
    # cross spaces X(a,b)
    def cross(a,b):
        Cst=np.array([[1,1,1,1,0,0,0,0],[0,0,0,0,1,1,1,1],[b,0,0,0]+list(a)],dtype=complex); u,s,vh=np.linalg.svd(Cst); out=[]
        for v in vh[3:].conj():
            M=np.zeros((4,5),complex); M[:,0]=v[:4]; M[0,1:]=v[4:]; out.append(M)
        return np.array(out)
    for a,b,lab in (((1,2,3,5),1,'cross a=(1,2,3,5), b=1'),((1,2,3,5),0,'cross b = 0 (z\' = 3)'),((1,1,1,1),1,'cross a in C1 (z = 3)')):
        n,err=T2test(cross(a,b),rg); print('%-26s dim of the solution space of (T2) = %3d;  distance of J\' from {sum_k T_k} + L_r: %.2e'%(lab,n,err),flush=True)
