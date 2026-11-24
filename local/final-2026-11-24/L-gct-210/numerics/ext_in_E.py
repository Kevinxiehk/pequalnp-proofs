import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
from core import *
def ext_search(L, e, starts=5, seed=0, tlimit=30, dc=False, verbose=False):
    """search level L+span(e vectors) with new vectors in E(L) (optionally ∩ DC)."""
    dE,E,s=ext_space(L)
    amb=E
    if dc:
        # intersect E with DC
        Dm=dc_ambient().reshape(16,-1); Em=E.reshape(len(E),-1)
        # solve a E + b D = 0
        M=np.vstack([Em,-Dm]).T; u,sv,vh=np.linalg.svd(M); k=np.sum(sv>1e-9*sv[0])
        ns=vh[k:].conj(); V=ns[:,:len(Em)]@Em
        amb=orth(V.reshape(-1,5,5)) if len(V) else np.zeros((0,5,5))
    rng=np.random.default_rng(seed); res=[]
    best=(np.inf,None)
    for st in range(starts):
        sB=np.einsum('ij,jab->iab',rng.normal(size=(e,len(amb)))+1j*rng.normal(size=(e,len(amb))),amb)
        fc,B=lm_space(sB,len(L)+e,fixed=L,ambient=amb,iters=200,tlimit=tlimit,rng=rng,verbose=verbose,rounds=4)
        res.append(fc)
        if fc<best[0]: best=(fc,B)
        if fc<1e-11: break
    return dE,len(amb),res,best
if __name__=='__main__':
    W=orth(weight_w5())
    for dc in [True,False]:
        for e in [1,2]:
            dE,na,res,(fc,B)=ext_search(W,e,starts=4,seed=e,dc=dc)
            print('W5 dc=%s e=%d: dimE=%d ambient=%d fresh per start'%(dc,e,dE,na),['%.1e'%r for r in res],flush=True)
            if fc<1e-10: print('   ',report('found',B)); np.save('W5ext_dc%d_e%d.npy'%(dc,e),B)
