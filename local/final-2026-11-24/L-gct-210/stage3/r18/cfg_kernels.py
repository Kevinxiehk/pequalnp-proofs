# Round 18: numerical members of the remaining (1,1,1,1,0) configurations and the outside-row kernel dims per pair (gauge + c(x)1 = 4 is minimal).
import numpy as np, itertools, sys
exec(open('/home/kevxhk/work/L-gct-210/stage3/r17/outside.py').read().split('w=np.array')[0])
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def srow_eqs(W):   # all single-row level conditions for rows W[0..3]: sigma_t-coefficients = P_R for every subset R of rows (|R| >= 1)
    out=[]
    for t in range(1,5):
        for R in itertools.combinations(range(4),t):
            M=np.array([W[i] for i in R]); out.append(sig(M,t,range(5)))
    return np.array(out)
def solve(param, nvar, extra):
    best=None
    for st in range(30):
        x=rg.normal(size=nvar)+1j*rg.normal(size=nvar)
        for it in range(200):
            F=lambda x: np.concatenate([srow_eqs(param(x)),extra(x)])
            f=F(x); Jm=np.array([(F(x+1e-7*np.eye(nvar)[i])-f)/1e-7 for i in range(nvar)]).T
            dx=np.linalg.lstsq(Jm,-f,rcond=None)[0]; x=x+dx
            if np.linalg.norm(F(x))<1e-12: break
        if np.linalg.norm(F(x))<1e-11: return x
    return None
nrm=lambda v,j: v/v[j]
cfgs={
 '(2,2)':  (lambda x: [np.r_[1,x[0:4]]]*2+[np.r_[x[4],1,x[5:8]]]*2, 8, lambda x: np.array([])),
 'k_N=2':  (lambda x: [np.r_[1,x[0:4]]]*2+[np.r_[1,x[4:8]],np.r_[1,x[8:12]]], 12, lambda x: np.array([x[12]*(np.r_[1,x[4:8]]@np.r_[1,x[4:8]])-1,x[13]*(np.r_[1,x[8:12]]@np.r_[1,x[8:12]])-1])),
 '(2,1,1)':(lambda x: [np.r_[1,x[0:4]]]*2+[np.r_[x[4],1,x[5:8]],np.r_[x[8],x[9],1,x[10:12]]], 12, lambda x: np.array([])),
 'k_N=4':  (lambda x: [np.r_[1,x[0:4]],np.r_[x[4],1,x[5:8]],np.r_[x[8],x[9],1,x[10:12]],np.r_[x[12],x[13],x[14],1,x[15]]], 16, lambda x: np.array([x[16+i]*(v@v)-1 for i,v in enumerate([np.r_[1,x[0:4]],np.r_[x[4],1,x[5:8]],np.r_[x[8],x[9],1,x[10:12]],np.r_[x[12],x[13],x[14],1,x[15]]])])),
}
for nm,(param,nv,extra) in cfgs.items():
    nvar=nv+len(extra(np.zeros(nv+4,complex)))
    x=solve(param,nvar,extra)
    if x is None: print(nm,': no member found'); continue
    W=np.array(param(x)); 
    # distinctness check for (2,1,1): rows 2,3 not parallel to m or each other
    print(nm,': member found; |single-row eqs| %.1e; kernel dims per pair (r,k):'%np.abs(srow_eqs(W)).max(), kernel_dims(W))
