# Round 17: stratum (II): rank of the x*-LINEAR conditions (d^1-coefficients of level + Delta-membership of c, D_2, D_3 of x = eta + d x*,
# x* = (r_0, r_1, -r_0-r_1)) at the numerical H-part solutions. If the 10 columns (r_0, r_1) have full rank, x* = 0 is forced there.
import numpy as np, itertools, glob
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
rg=np.random.default_rng(5); AB=rg.normal(size=(10,2))+1j*rg.normal(size=(10,2))
def conds(h,xs,d):
    d0=h[0]-h[2]; d1=h[1]-h[2]; Dl=np.stack([d0,d1],1); Pj=np.eye(5)-Dl@np.linalg.pinv(Dl); out=[]
    for a,b in AB:
        X=np.array([a*h[0],b*h[1],(-a-b)*h[2]])+d*xs
        out+=[sig(X,m,range(5)) for m in (1,2,3)]
        for m in (1,2,3):
            v=np.array([sig(X,m,[c for c in range(5) if c!=j]) for j in range(5)]); out+=list(Pj@v)
    return np.array(out)
def d1(h,xs):   # exact d^1 coefficient: conditions are polynomials of degree <= 3 in d -> fit on 4 points
    ds=np.array([0.5,-0.5,1.0,-1.0]); V=np.array([conds(h,xs,d) for d in ds]); Mv=np.vander(ds,4,increasing=True)
    C=np.linalg.solve(Mv,V); return C[1]
for f in sorted(glob.glob('/home/kevxhk/work/L-gct-210/stage3/r16/st2num_full_*.npy')):
    h=np.load(f)[:15].reshape(3,5); cols=[]
    for k in range(10):
        r=np.zeros(10,complex); r[k]=1; xs=np.array([r[:5],r[5:],-r[:5]-r[5:]]); cols.append(d1(h,xs))
    A=np.array(cols).T; s=np.linalg.svd(A,compute_uv=False)
    print(f.split('/')[-1],'A',A.shape,'sing.vals:',np.round(s/s[0],8))
