# r=8 (L = X_A + X_B, dim 8) with P_2 = 0 and Frobenius-Koenig block conditions only (no P_3..P_5):
# for every p x q block K with p+q=6 (types given), a functional n_K with n_K(J_K)=1 kills L|_K.
import sys, time, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/lowd')
import numpy as np
from d1lm import DCB, ROW, COL, rnd
types=sys.argv[1].split(',')   # e.g. 15,51,24,42
usep2=int(sys.argv[2]); starts=int(sys.argv[3]); seed=int(sys.argv[4]); tl=float(sys.argv[5])
blocks=[]
for ty in types:
    p,q=int(ty[0]),int(ty[1])
    for R in itertools.combinations(range(5),p):
        for C in itertools.combinations(range(5),q):
            blocks.append([(i,j) for i in R for j in C])
rng=np.random.default_rng(seed); t0=time.time()
AB=np.concatenate([ROW,COL])
nb=len(blocks); sizes=[len(K) for K in blocks]
# complement bases
CB=[]
for K in blocks:
    m=len(K); Bm=np.zeros((m-1,m)); 
    for a in range(m-1): Bm[a,a]=1; Bm[a,m-1]=-1
    CB.append(Bm)
nY=128; nN=sum(s-1 for s in sizes); npar=nY+nN
offs=np.cumsum([0]+[s-1 for s in sizes])
def basis(p):
    Y=p[:nY].reshape(8,16); return AB+np.einsum('km,mab->kab',Y,DCB)
for s in range(starts):
    p=0.5*rnd(npar,rng)
    def resjac(p):
        Bs=basis(p)  # 8x5x5
        rows=[]; J=[]
        # dB/dY: d basis k / d Y[k,m] = DCB[m]
        if usep2:
            S=Bs.sum(2); Cc=Bs.sum(1)
            for i in range(8):
                for j in range(i,8):
                    val=0.5*((Bs[i]*Bs[j]).sum()-S[i]@S[j]-Cc[i]@Cc[j])
                    g=np.zeros(npar,complex)
                    # derivative wrt Y[i,m]: 0.5*(<DCB_m,Bs[j]> - rowsum(DCB_m).S[j] - colsum(DCB_m).C[j]) ; DCB has zero row/col sums
                    gi=0.5*np.einsum('mab,ab->m',DCB,Bs[j]); gj=0.5*np.einsum('mab,ab->m',DCB,Bs[i])
                    g[16*i:16*i+16]+=gi; g[16*j:16*j+16]+=gj
                    rows.append(val); J.append(g)
        for b,K in enumerate(blocks):
            idx=np.array(K); m=len(K)
            nK=np.ones(m)/m+p[nY+offs[b]:nY+offs[b+1]]@CB[b]
            vals=Bs[:,idx[:,0],idx[:,1]]  # 8 x m
            DK=DCB[:,idx[:,0],idx[:,1]]   # 16 x m
            for k in range(8):
                rows.append(nK@vals[k])
                g=np.zeros(npar,complex)
                g[16*k:16*k+16]=DK@nK
                g[nY+offs[b]:nY+offs[b+1]]=CB[b]@vals[k]
                J.append(g)
        return np.array(rows),np.array(J)
    lam=1e-3; r,J=resjac(p); f=np.linalg.norm(r)
    for it in range(400):
        if time.time()-t0>tl: break
        H=J.conj().T@J; gg=J.conj().T@r
        pn=p+np.linalg.solve(H+lam*np.diag(np.diag(H).real+1e-6)+1e-14*np.eye(npar),-gg)
        rn,Jn=resjac(pn); fn=np.linalg.norm(rn)
        if fn<f: p=pn; r,J=rn,Jn; f=fn; lam=max(lam/3,1e-12)
        else:
            lam*=4
            if lam>1e8: break
        if f<1e-12: break
    print(f'types={types} P2={usep2} start {s}: res {f:.2e} it {it}  #eq {len(r)} #unk {npar}',flush=True)
    np.save(f'fk_{sys.argv[1].replace(",","_")}_{usep2}_{s}.npy',basis(p))
    if time.time()-t0>tl: break
