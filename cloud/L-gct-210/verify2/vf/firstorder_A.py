# verify2 round 6: independent look at VF-A.  First-order extension space of the plane N inside A_m:
#   T(N) := { E in A_m : d/dx R_i(k Z + t Zs + x E) at x = 0 vanishes identically in (k,t), i = 1..4 }  (contains N).
# If T(N) = N there is no one-vector extension at all, by linear algebra only.
import numpy as np, itertools
P4=list(itertools.permutations(range(4)))
w=np.exp(2j*np.pi/3); m=np.array([1,w,w*w,0,0]); mbar=np.array([1,w*w,w,0,0])
one=np.ones(4); chi1=np.array([1,1j,-1,-1j]); chi2=np.array([1,-1,1,-1])
def cvec(Y):
    U=1+Y; out=np.empty(5,complex)
    for j in range(5):
        A=np.delete(U,j,axis=1); out[j]=sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)-24
    return out
def grad_c(Y):
    """Jacobian of c at Y: (5, 4, 5) array, d c_j / d Y[r,c] = perm_3 of (1+Y) without row r and columns j, c"""
    U=1+Y; G=np.zeros((5,4,5),complex); P3=list(itertools.permutations(range(3)))
    for j in range(5):
        for r in range(4):
            rows=[x for x in range(4) if x!=r]
            for c in range(5):
                if c==j: continue
                cols=[x for x in range(5) if x not in (j,c)]; A=U[np.ix_(rows,cols)]
                G[j,r,c]=sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]] for p in P3)
    return G
Wm=np.array([[0,0,0,1,0],[0,0,0,0,1],[w,-1,0,0,0],[w*w,0,-1,0,0]])
# basis of A_m: rows 0..2 free, lambda
def Ebasis():
    B=[]
    for r in range(3):
        for c in range(5):
            E=np.zeros((4,5),complex); E[r,c]=1; E[3,c]=-1; B.append(E)
    E=np.zeros((4,5),complex); E[3]=m; B.append(E); return np.array(B)
EB=Ebasis(); rng=np.random.default_rng(0)
for sb in (1,-1):
    for sx in (1,-1):
        beta=sb*np.sqrt(3)/4; xi=sx*np.sqrt(complex(-3/(32*beta)))
        Z=np.outer(one/4+beta*chi2,m)+np.outer(chi1,[0,xi,-xi,0,0]); Zs=np.outer(chi1,mbar)
        rows=[]
        for _ in range(40):
            k,t=rng.normal(size=2)+1j*rng.normal(size=2); G=grad_c(k*Z+t*Zs)        # (5,4,5)
            D=np.einsum('jrc,nrc->jn',G,EB)                                         # (5,16): derivative of c_j along each basis E
            rows.append(Wm@D)                                                       # (4,16)
        A=np.concatenate(rows); s=np.linalg.svd(A,compute_uv=False); rk=int(np.sum(s>1e-9*s[0]))
        # N in coordinates
        print('beta %+d xi %+d: first-order system rank %d of 16 (singular values around the cut: %.2e | %.2e) -> dim T(N) = %d'%(sb,sx,rk,s[rk-1],s[rk] if rk<16 else 0,16-rk))
# calibration: N replaced by span(Zs)
rows=[]
for _ in range(40):
    t=rng.normal()+1j*rng.normal(); G=grad_c(t*Zs); rows.append(Wm@np.einsum('jrc,nrc->jn',G,EB))
s=np.linalg.svd(np.concatenate(rows),compute_uv=False); rk=int(np.sum(s>1e-9*s[0])); print('calibration span(Zs): rank %d -> first-order extension space of dim %d (contains Zs)'%(rk,16-rk))
