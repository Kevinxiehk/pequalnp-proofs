# Round 9, target 3: skew deformations of a FULL FREE ROW (4-dim row block): M_F = e_r (x) 1^perp (+) N (Type F), deformed to
# { e_r w^T + t e_j (B w)^T : w in 1^perp } with B skew for the bilinear form on 1^perp (random skew S, B = G^{-1} S in a basis).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import level_err, null, rowpart
from a5 import onb
from nc_num import report
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
for f in ('M_L080_col0.npy','M_ex2_row4.npy'):
    B0=onb(np.load(f)); r=[i for i in range(4) if len(rowpart(B0,[i]))==4][0]
    FR=rowpart(B0,[r]); W=FR[:,r,:]                      # 4 x 5 basis of 1^perp (free row)
    others=[b for b in B0]
    # N = complement of the free row in M_F
    Pf=FR.reshape(4,-1); Q=np.linalg.qr(Pf.conj().T)[0]; Bf=B0.reshape(len(B0),-1); Rr=Bf-(Bf@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(Rr,full_matrices=False); N=vh[:int((s>1e-8).sum())].reshape(-1,4,5)
    G=W@W.T
    for trial in range(3):
        S=rg.normal(size=(4,4))+1j*rg.normal(size=(4,4)); S=S-S.T; Bm=np.linalg.solve(G,S)   # coefficient-level skew map
        for j in [k for k in range(4) if k!=r]:
            t=0.6+0.3j; El=[]
            for k in range(4):
                m=np.zeros((4,5),complex); m[r]=W[k]; m[j]=t*(Bm[:,k]@W); El.append(m)
            M=np.concatenate([np.array(El),N],0)
            le=level_err(onb(M),ntest=15)
            if le<1e-8: report('%s free row %d -> row %d (random skew B #%d)'%(f,r,j,trial),M)
            else: print('%s free row %d -> row %d #%d: NOT level (%.1e)'%(f,r,j,trial,le))
# LM search for special skew B (6 complex unknowns) making the deformed space level
from ext6 import F45
def search(f,j,starts=20):
    B0=onb(np.load(f)); r=[i for i in range(4) if len(rowpart(B0,[i]))==4][0]
    FR=rowpart(B0,[r]); W=FR[:,r,:]; Pf=FR.reshape(4,-1); Q=np.linalg.qr(Pf.conj().T)[0]; Bf=B0.reshape(len(B0),-1); Rr=Bf-(Bf@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(Rr,full_matrices=False); N=vh[:int((s>1e-8).sum())].reshape(-1,4,5); G=W@W.T
    iu=np.triu_indices(4,1); C=rg.normal(size=(120,6))+1j*rg.normal(size=(120,6)); found=[]
    def build(z):
        S=np.zeros((4,4),complex); S[iu]=z; S=S-S.T; Bm=np.linalg.solve(G,S); El=[]
        for k in range(4):
            m=np.zeros((4,5),complex); m[r]=W[k]; m[j]=Bm[:,k]@W; El.append(m)
        return np.concatenate([np.array(El),N],0)
    def res(z): return F45(np.einsum('nk,kij->nij',C,build(z)))-120
    for st in range(starts):
        z=rg.normal(size=6)+1j*rg.normal(size=6); r_=res(z); c=np.linalg.norm(r_)
        for it in range(60):
            J=np.empty((len(r_),6),complex)
            for a in range(6):
                zp=z.copy(); zp[a]+=1e-7; J[:,a]=(res(zp)-r_)/1e-7
            dz=np.linalg.lstsq(J,-r_,rcond=None)[0]; zn=z+dz; rn=res(zn)
            if np.linalg.norm(rn)<c: z,r_,c=zn,rn,np.linalg.norm(rn)
            else: z=z+0.3*dz; r_=res(z); c=np.linalg.norm(r_)
            if c<1e-11: break
        if c<1e-9 and np.abs(z).max()>1e-4: found.append(z)
    print('%s row %d -> %d: %d nonzero skew solutions in %d starts'%(f,r,j,len(found),starts),flush=True)
    for z in found[:1]: report('   solution',build(z))
for f in ('M_L080_col0.npy','M_ex2_row4.npy'):
    for j in range(3): search(f,j)
print('--- rank of the skew map B in the solutions, and line parts')
from pieces import analyse
def search2(f,j,starts=6):
    B0=onb(np.load(f)); r=[i for i in range(4) if len(rowpart(B0,[i]))==4][0]
    FR=rowpart(B0,[r]); W=FR[:,r,:]; Pf=FR.reshape(4,-1); Q=np.linalg.qr(Pf.conj().T)[0]; Bf=B0.reshape(len(B0),-1); Rr=Bf-(Bf@Q.conj())@Q.T
    u,s,vh=np.linalg.svd(Rr,full_matrices=False); N=vh[:int((s>1e-8).sum())].reshape(-1,4,5); G=W@W.T
    iu=np.triu_indices(4,1); C=rg.normal(size=(120,6))+1j*rg.normal(size=(120,6))
    def build(z):
        S=np.zeros((4,4),complex); S[iu]=z; S=S-S.T; Bm=np.linalg.solve(G,S); El=[]
        for k in range(4):
            m=np.zeros((4,5),complex); m[r]=W[k]; m[j]=Bm[:,k]@W; El.append(m)
        return np.concatenate([np.array(El),N],0),S
    def res(z): return F45(np.einsum('nk,kij->nij',C,build(z)[0]))-120
    for st in range(starts):
        z=rg.normal(size=6)+1j*rg.normal(size=6); r_=res(z); c=np.linalg.norm(r_)
        for it in range(60):
            J=np.empty((len(r_),6),complex)
            for a in range(6):
                zp=z.copy(); zp[a]+=1e-7; J[:,a]=(res(zp)-r_)/1e-7
            dz=np.linalg.lstsq(J,-r_,rcond=None)[0]; zn=z+dz; rn=res(zn)
            if np.linalg.norm(rn)<c: z,r_,c=zn,rn,np.linalg.norm(rn)
            else: z=z+0.3*dz; r_=res(z); c=np.linalg.norm(r_)
            if c<1e-11: break
        if c<1e-9:
            M,S=build(z); sv=np.linalg.svd(S,compute_uv=False); l1,out=analyse(onb(M))
            print('%s %d->%d: rank S = %d (sv %s); line rank %d, non-line pieces %s'%(f,r,j,int((sv>1e-6*sv[0]).sum()),np.round(sv/sv[0],3),l1,[(k,idx,dP,a,s_) for (k,idx,dP,a,s_) in out]),flush=True)
for f in ('M_L080_col0.npy','M_ex2_row4.npy'): search2(f,0)
