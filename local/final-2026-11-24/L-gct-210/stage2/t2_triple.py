import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import *
rng=np.random.default_rng(11)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def emb(i,v,ip,vp):
    w=np.zeros((3,5),complex); w[i]=v; w[ip]=vp; return w.reshape(-1)
def triple(kap1,e12,e13):
    e12=np.array(e12); e13=np.array(e13); e23=e12*e13
    k2,nu12,nup12,c12,s12=typeI(kap1,e12)
    k3,nu13,nup13,c13,s13=typeI(kap1,e13)
    k3b,nu23,nup23,c23,s23=typeI(k2,e23)
    if np.abs(k3b-k3).max()>1e-9:
        k3c,nu23,nup23,c23,s23=typeI(k2,-e23)
        assert np.abs(k3c-k3).max()<1e-9, 'inconsistent'
    N=np.array([emb(0,kap1,1,-k2),emb(0,kap1,2,-k3),emb(0,nu12,1,nup12),emb(0,nu13,2,nup13),emb(1,nu23,2,nup23)])
    return N,(kap1,k2,k3)
def test(kap1,e12,e13,verbose=False):
    N,(k1,k2,k3)=triple(kap1,e12,e13)
    rN=rank(N)
    I3=nullspace(N)   # 15 x (15-rN)
    J3=np.ones(15); assert np.abs(N@J3).max()<1e-9
    res=[]
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]
        # Pi_S = I3 cap {entries in columns Sc =0}
        rows=[i*5+c for i in range(3) for c in Sc]
        K=nullspace(I3[rows,:]); P=I3@K; d=P.shape[1]
        ellv=np.zeros(15,complex); ellv[:5]=k1; ell=ellv@P
        B1=np.abs(ell).max()>1e-9
        # test perm_3 = k ell^3 on Pi_S
        vals=[]
        for _ in range(8):
            cf=rnd(d); z=(P@cf).reshape(3,5)[:,list(S)]; vals.append((perm(z),(ell@cf)**3))
        vals=np.array(vals)
        if B1:
            k=vals[0,0]/vals[0,1]; ok=np.abs(vals[:,0]-k*vals[:,1]).max()<1e-7*max(1,np.abs(vals[:,0]).max()); 
            res.append((S,d,'ell!=0','cube' if ok else 'NOTCUBE', abs(k) if ok else None))
        else:
            z0=np.abs(vals[:,0]).max()<1e-8
            res.append((S,d,'ell=0','perm3=0' if z0 else 'perm3!=0 (needs perm2=0 on U_S)',None))
    return rN,res
pats=[e for e in itertools.product([1,-1],repeat=5) if e[0]==1 and abs(sum(e))<5]
summary={}
for e12 in pats:
    for e13 in pats:
        if e13<=e12: continue
        kap1=rnd(5); kap1/=kap1.sum()
        rN,res=test(kap1,e12,e13)
        nbad=sum(1 for r in res if r[3]=='NOTCUBE'); dims=sorted(set(r[1] for r in res))
        key=(rN,nbad,tuple(dims)); summary[key]=summary.get(key,0)+1
        if nbad==0: print('NO VIOLATION for',e12,e13,[(r[0],r[1],r[2],r[3]) for r in res])
print('summary (rank N, #triples S with perm3 not a cube, dims of Pi_S) -> count:'); 
for k,v in sorted(summary.items()): print('  ',k,v)
kap1=rnd(5); kap1/=kap1.sum(); rN,res=test(kap1,pats[2],pats[7]); print(pats[2],pats[7],rN); [print('  ',r) for r in res]
