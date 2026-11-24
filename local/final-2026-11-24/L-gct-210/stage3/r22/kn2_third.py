# numerical third elements of X_{rk} for the k_N = 2 block member (m = (1,w^2,w,0,0) rows 0,1; n2 = (0,0,0,1,-1), n3 = (2,2,2,-3,-3)), and a compatibility
# test: is span(single-row elements, xi_02, xi_12, xi_23...) level?
import numpy as np, itertools, sys
w=np.exp(2j*np.pi/3)
W=np.array([[1,w**2,w,0,0],[1,w**2,w,0,0],[0,0,0,1,-1],[2,2,2,-3,-3]],complex)
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
rg=np.random.default_rng(int(sys.argv[3]) if len(sys.argv)>3 else 0)
S=rg.normal(size=(16,5))+1j*rg.normal(size=(16,5))
def third(r,k,NS):
    l,n=[i for i in range(4) if i not in (r,k)]
    def build(x):
        xi=np.zeros((5,5),complex); xi[l]=x[0:5]; xi[n]=x[5:10]; xi[4]=x[10:15]; return xi
    gl=int(np.argmax(np.abs(W[l]))); gn=int(np.argmax(np.abs(W[n])))
    NRM=rg.normal(size=15)+1j*rg.normal(size=15)
    def F(x):
        xi=build(x); out=[x[gl],x[5+gn],NRM@x-1]
        for co in S:
            X=co[0]*xi; 
            for i in range(4): X[i]=X[i]+co[1+i]*W[i]
            out+=[sig(X,m,range(5)) for m in range(1,6)]
        return np.array(out)
    sols=[]
    for st in range(NS):
        x=rg.normal(size=15)+1j*rg.normal(size=15); lam=1e-2
        for it in range(200):
            f=F(x); nf=np.linalg.norm(f)
            if nf<1e-12: break
            Jm=np.array([(F(x+1e-7*np.eye(15)[i])-f)/1e-7 for i in range(15)]).T
            A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
            for _ in range(10):
                dx=np.linalg.solve(A+lam*np.eye(15),g)
                if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
                lam*=4
            if not ok: break
        if np.linalg.norm(F(x))<1e-9: sols.append(build(x))
    return sols
r,k=int(sys.argv[1]),int(sys.argv[2])
sols=third(r,k,8)
for s in sols:
    nz=[(i,j) for i in range(5) for j in range(5) if abs(s[i,j])>1e-7]
    print('pair (%d,%d) third element support (row,col):'%(r,k),nz)
    print(np.round(s/ s[nz[0]] if nz else s,4))
