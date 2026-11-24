# numerical check of the ingredients of Lemma O3 on degree-2 solutions B_a+B_b+B_c = 1 (B_j in O(3,C)), via sl_2:
# V = sl_2 with <x,y> = tr(xy)/2 ... realised by an explicit isometry; B_j = eps_j Ad(g_j); check s = sum eps in {1,-3},
# sum eps_j g_j (x) adj(g_j) = 1(x)1 (s=1) / tr g_j = 0 (s=-3), and the conclusion.
import numpy as np, sys
exec(open('deg2.py').read().split("for st in range")[0])
# basis of sl_2 orthonormal for the form <x,y> = tr(xy)/2 : e1 = [[1,0],[0,-1]], e2 = [[0,1],[1,0]], e3 = [[0,-1j],[1j,0]]... use complex-orthonormal
E=[np.array([[1,0],[0,-1]],complex),np.array([[0,1],[1,0]],complex),np.array([[0,1],[-1,0]],complex)*1j]
G=np.array([[np.trace(a@b)/2 for b in E] for a in E]); print('Gram of sl2 basis',np.round(G,3).tolist())
def toM(v): return sum(v[i]*E[i] for i in range(3))
def fromM(M): return np.array([np.trace(M@E[i])/2 for i in range(3)])
def lift(B):  # find eps, g with B v = eps g v g^-1: solve linear equations g X = (eps B X) g for X in basis
    for eps in (1,-1):
        A=[]
        for i in range(3):
            X=E[i]; Y=toM(eps*(B@np.eye(3)[i]))
            # g X - Y g = 0  -> linear in the 4 entries of g
            for r in range(2):
                for c in range(2):
                    row=np.zeros(4,complex)
                    for k in range(2):
                        row[2*r+k]+=X[k,c]; row[2*k+c]-=Y[r,k]
                    A.append(row)
        A=np.array(A); u,s,vh=np.linalg.svd(A)
        if s[-1]<1e-8*s[0]:
            g=vh[-1].conj().reshape(2,2); g/=np.sqrt(np.linalg.det(g)); return eps,g
    return None
rng=np.random.default_rng(5); nsol=0
for st in range(40):
    x=rng.normal(size=18)+1j*rng.normal(size=18); lam=1e-3; f=res(x); nf=np.linalg.norm(f)
    for it in range(300):
        if nf<1e-13: break
        J=jac(x,f); dx=np.linalg.lstsq(J.conj().T@J+lam*np.eye(18),-J.conj().T@f,rcond=None)[0]; f2=res(x+dx)
        if np.linalg.norm(f2)<nf: x=x+dx; f=f2; nf=np.linalg.norm(f2); lam=max(lam/3,1e-14)
        else: lam*=4
    if nf>1e-11: continue
    nsol+=1
    Bs=[x[:9].reshape(3,3),x[9:].reshape(3,3)]; Bs.append(np.eye(3)-Bs[0]-Bs[1])
    L=[lift(B) for B in Bs]; eps=[l[0] for l in L]; gs=[l[1] for l in L]; s=sum(eps)
    T=sum(e*np.kron(g,np.linalg.inv(g)) for e,g in zip(eps,gs))   # tensor sum eps g (x) g^-1 (Kronecker form)
    target=np.kron(np.eye(2),np.eye(2))
    rk=[int(np.sum(np.linalg.svd((np.eye(3)-B)/2,compute_uv=False)>1e-6)) for B in Bs]
    print('s=%2d  |T - 1(x)1|=%.1e  tr g=%s  ranks A=%s'%(s,np.linalg.norm(T-target) if s==1 else -1,np.round([abs(np.trace(g)) for g in gs],4),rk))
print('solutions',nsol)
