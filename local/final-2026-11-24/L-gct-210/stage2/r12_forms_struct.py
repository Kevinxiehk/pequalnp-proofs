# Structure of the FO2-joint forms on T_1(X)/X for X = P + e_i (x) Z (z_i = 3): ranks of q_0 and B_z, and of generic combinations.
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(3)
f=A_[1]; irow=int(A_[2]); zidx=[int(c) for c in A_[3].split(',')]
Bf=np.load(f); X=np.zeros((len(Bf),5,5),complex); X[:,1:,:]=Bf; Xf=X.reshape(len(Bf),25)
u,s,vh=np.linalg.svd(Xf,full_matrices=False); Xo=vh[:5]
rows=[cof55(np.ones((5,5))+((rg.normal(size=5)+1j*rg.normal(size=5))@Xo).reshape(5,5)) for _ in range(80)]
u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-8*s[0]).sum()); T=vh[r:].conj()
Pj=T-(T@Xo.conj().T)@Xo; u,s,vh=np.linalg.svd(Pj); Q=vh[:len(T)-5]; nq=len(Q)
def rk(M,tol=1e-8): sv=np.linalg.svd(M,compute_uv=False); return int((sv>tol*max(sv[0],1e-300)).sum())
q0=Q@hess(np.ones((5,5)))@Q.T
print('dim T_1',len(T),'complement',nq,' rank q0 =',rk(q0))
Bs=[]
for k in zidx:
    H1=hess(np.ones((5,5))+X[k]); Bz=Q@(H1-hess(np.ones((5,5))))@Q.T; Bs.append(Bz)
    print('  B_z for z = row %d of basis %d: rank %d'%(irow,k,rk(Bz)))
G=sum((rg.normal()+1j*rg.normal())*b for b in Bs); print('  generic combination of the B_z: rank',rk(G))
K=np.vstack(Bs); print('  common kernel of all B_z (in complement):',nq-rk(K))
# is q_m affine in s along e_i z ? check q_{2 m} - q_0 = 2 (q_m - q_0)
H2=hess(np.ones((5,5))+2*X[zidx[0]]); H1=hess(np.ones((5,5))+X[zidx[0]]); H0=hess(np.ones((5,5)))
print('  affinity check |q_2m - q_0 - 2(q_m - q_0)| =',np.abs(H2-H0-2*(H1-H0)).max())
# image of the row-r projection of the complement and of T_1
print('  T_1 row-0 projection dim',rk(T.reshape(len(T),5,5)[:,0,:]))
