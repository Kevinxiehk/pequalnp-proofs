# LEMMA SC check on column-centred 4x5 level 4-spaces: defect dimension, neutral columns, single-column elements, and the rank of the
# SC map Y -> (x.Y_{:,l})_{l != s} for each single-column element x e_s^T.
import sys, numpy as np, itertools
perms=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in perms)
def R(Y): JY=1+Y; return np.array([perm4(np.delete(JY,k,axis=1))-24 for k in range(5)])
for f in sys.argv[1:]:
    B=np.load(f); B=B.reshape(B.shape[0],4,5); D=B.shape[0]
    rng=np.random.default_rng(0); V=[]
    for _ in range(40):
        c=rng.normal(size=D)+1j*rng.normal(size=D); t=rng.normal()+1j*rng.normal()
        V.append(R(t*np.tensordot(c,B,axes=(0,0))))
    V=np.array(V); s=np.linalg.svd(V,compute_uv=False); e=int((s>1e-7*s[0]).sum())
    _,_,vh=np.linalg.svd(V); Cb=vh[:e]                       # rows span C (Hermitian basis of the row space)
    neutral=[(j,float("%.1e"%np.linalg.norm(Cb[:,j]))) for j in range(5) if np.linalg.norm(Cb[:,j])<1e-3]
    out=[]
    for sc in range(5):
        M=np.concatenate([np.delete(B[k],sc,axis=1).ravel()[None,:] for k in range(D)],0)   # coefficients of columns != sc
        u,sv,vh2=np.linalg.svd(M.T); null=[vh2[i].conj() for i in range(D) if i>=len(sv) or sv[i]<1e-4*sv[0]]
        for n in null:
            Y=np.tensordot(n,B,axes=(0,0)); x=Y[:,sc]
            if np.linalg.norm(x)<1e-9: continue
            Mmap=np.array([[x@B[k][:,l] if l!=sc else 0 for l in range(5)] for k in range(D)])
            rk=np.linalg.matrix_rank(Mmap,1e-4)
            # is the image inside C?
            res=max(np.linalg.norm(v-(v@Cb.conj().T)@Cb) for v in Mmap)
            out.append('single-col in col %d: SC-map rank %d, image-in-C resid %.1e'%(sc,rk,res))
    print(f.split('/')[-1],': dim',D,'e =',e,'sv',np.array2string(s[:5]/s[0],precision=1),'neutral cols',neutral,'|',' ; '.join(out) if out else 'no single-column element')
