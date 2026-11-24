# Round 11: the family N(w2,w3) = F_4 (+) C e_2 w2^T (+) C e_3 w3^T (F_4 = column-0 vectors on rows 0..3 with sum 0; w2, w3 in V0 =
# {w_0 = 0, sum w = 0}, <w2,w3> = 0), embedded in 5x5 with row 4 = 0.  Exact level check, T_1, the forms q_m (m in N) on V = T_1/N,
# dimension of their span, and the sigma_2 / FO2 bounds.   usage: python3 -I ncdef_fo2.py SEED [file]
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2'); import fo2lib as F
seed=int(sys.argv[1]); rg=np.random.default_rng(seed)
def member(w2,w3):
    B=[]
    for (i,k) in ((0,1),(1,2),(2,3)):                 # F_4 basis: e_i - e_k in column 0
        M=np.zeros((5,5),complex); M[i,0]=1; M[k,0]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[2]=w2; B.append(M); M=np.zeros((5,5),complex); M[3]=w3; B.append(M); return np.array(B)
def rv(): return rg.normal(size=4)+1j*rg.normal(size=4)
if len(sys.argv)>2:
    Z=np.load(sys.argv[2]); B=np.zeros((5,5,5),complex); B[:,:4,:]=Z; tag='file'
else:
    a=rv(); a-=a.mean(); w2=np.concatenate([[0],a])
    b=rv(); b-=b.mean(); bb=np.concatenate([[0],b]); u=np.concatenate([[0],np.ones(4)])
    # w3 in V0 orthogonal (bilinear) to w2: project b onto {s = 0, <.,w2> = 0} inside columns 1..4
    A=np.array([u[1:],w2[1:]]); ns=np.linalg.svd(A)[2][2:].conj(); w3=np.concatenate([[0],ns.T@(ns.conj()@b)])   # any vector in the null space
    B=member(w2,w3); tag='random member'
d=len(B); J=np.ones((5,5))
def pt(): return J+np.tensordot(rg.normal(size=d)+1j*rg.normal(size=d),B,axes=1)
lev=max(abs(F.perm_small(pt())-120) for _ in range(20)); print(tag,': level error %.1e'%lev)
A=np.array([F.cof(pt()) for _ in range(160)]); Nb,s=F.null(A); n=Nb.shape[1]
print('dim T_1 =',n,' (sv gap %.1e / %.1e)'%(s[25-n-1]/s[0], s[25-n]/s[0] if n>0 else 0))
Bv=B.reshape(d,25).T                                        # 25 x d
# coordinates: T_1 = N (+) V ; express N inside T_1
X=np.linalg.lstsq(Nb,Bv,rcond=None)[0]                     # n x d : coords of N's basis in T_1 basis
print('N inside T_1: residual %.1e'%np.abs(Nb@X-Bv).max())
Qc=np.linalg.qr(np.concatenate([X,rg.normal(size=(n,n-d))+1j*rg.normal(size=(n,n-d))],1))[0]
Vb=Nb@Qc[:,d:]                                              # 25 x (n-d): complement of N in T_1 (generic)
G=[]
for _ in range(40):
    H=F.hess(pt()); GT=Nb.T@H@Nb
    G.append(GT)
rad=max(np.abs(GT@X).max() for GT in G[:5]); print('N in the radical of q_m on T_1: %.1e'%rad)
GV=[Vb.T@F.hess(pt())@Vb for _ in range(40)]               # forms on the complement (= on V, since N is radical)
iu=np.triu_indices(n-d); Mx=np.array([g[iu] for g in GV]); sv=np.linalg.svd(Mx,compute_uv=False)
k=int((sv>1e-8*sv[0]).sum()); print('span of {q_m restricted to V} (V = T_1/N, dim %d): dim %d   sv %s'%(n-d,k,np.round(sv[:k+2]/sv[0],8)))
for i in range(3):
    r=np.linalg.matrix_rank(GV[i],1e-8*np.abs(GV[i]).max()); print('  rank of a single q_m on V: %d -> max isotropic %d -> bound %d'%(r,(n-d-r)+r//2,d+(n-d-r)+r//2))
np.save('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_forms_%s_%d.npy'%(tag.split()[0],seed),np.array(GV)); np.save('/home/kevxhk/work/L-gct-210/stage3/r11/ncdef_basis_%s_%d.npy'%(tag.split()[0],seed),np.concatenate([Bv.T,Vb.T]).reshape(-1,5,5))
