import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/numerics/r2")
from spaces import *
np.set_printoptions(precision=3,suppress=True,linewidth=170)
for nm,B in [('ex1',ex1()),('ex2',ex2())]:
    L=orth(B); dE,E,s=ext_space(L)
    print(nm,'dimE',dE,'E level? fresh %.2e'%fresh_check(E))
    # extra direction mod L
    Lm=L.reshape(7,-1); Em=E.reshape(dE,-1)
    R=Em-(Em@Lm.conj().T)@Lm; u,sv,vh=np.linalg.svd(R); v=vh[0].reshape(5,5)
    v=v/v.flat[np.argmax(abs(v))]
    print(' extra direction (mod L, orth to L):\n',np.round(v,3))
    # which P_k fail on L+v
    Q=orth(np.concatenate([L,v[None]])); rng=np.random.default_rng(1)
    x=rng.normal(size=(30,8))+1j*rng.normal(size=(30,8)); x/=np.linalg.norm(x,axis=1,keepdims=True)
    print(' max|P_k| on L+v, k=1..5:',np.abs(Pk(np.einsum('ri,iab->rab',x,Q))[:,1:]).max(0))
    # 6-dim subspaces: generic and coordinate (drop basis vector i)
    rng=np.random.default_rng(2)
    for tr in range(3):
        C=rng.normal(size=(6,7))+1j*rng.normal(size=(6,7)); S=orth(np.einsum('ij,jab->iab',C,L))
        dS,ES,sS=ext_space(S); print(f' generic S{tr}: dimE(S)={dS} gap {sS[24-dS]:.1e}/{sS[25-dS]:.1e} E(S) level? {fresh_check(ES):.1e}' if dS>7 else f' generic S{tr}: dimE(S)={dS}')
    for i in range(7):
        S=orth(np.delete(B,i,axis=0)); dS,ES,sS=ext_space(S)
        print(f' S = drop basis vec {i}: inv {invariants(S)} dimE(S)={dS} gap {sS[24-dS]:.1e}/{sS[25-dS]:.1e}',flush=True)
