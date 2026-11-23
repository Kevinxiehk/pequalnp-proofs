import sys; sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from tangent import *
np.set_printoptions(precision=3,suppress=True,linewidth=150)
for n in [4,5]:
    B=np.array(construction_2n3(n),dtype=complex); d=len(B)
    rng=np.random.default_rng(0)
    xs=rng.normal(size=(400,d))+1j*rng.normal(size=(400,d))
    P,G=Pk_grad(np.einsum('ri,iab->rab',xs,B))
    rows=G[:,1:].reshape(-1,n*n); nr=np.linalg.norm(rows,axis=1); rows=rows[nr>1e-9*nr.max()]
    u,s,vh=np.linalg.svd(rows); ns=vh[np.sum(s>1e-8*s[0]):].conj()
    # remove L component
    Lf=B.reshape(d,-1).T; Qf,_=np.linalg.qr(Lf)
    R=ns.T-Qf@(Qf.conj().T@ns.T)
    u2,s2,_=np.linalg.svd(R); t=u2[:,0].reshape(n,n); t=t/t[np.unravel_index(np.argmax(abs(t)),t.shape)]
    print(n,'extra direction (mod L):\n',t.real)
    # which P_k fail on L+t ?
    B2=np.concatenate([B,t[None]]); print(' worst |P_k| on L+t:',check_numeric(B2,n))
