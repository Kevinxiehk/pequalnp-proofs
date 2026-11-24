# verify2 r25: search for a recursive-kernel-bound contradiction at an exact parameter value (rational or algebraic via sympy), my own code.
# usage: python3 -I chain_search.py CACHE "value expression" [maxdepth]
import pickle, sys, sympy as sp, random
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(sys.argv[1],'rb'))
val=sp.sympify(sys.argv[2]) if par else None; MAXD=int(sys.argv[3]) if len(sys.argv)>3 else 7
def S(M): return M.applyfunc(lambda x: sp.nsimplify(sp.expand(x)) if val is not None and val.is_rational else sp.radsimp(sp.expand(x)))
G=[S(g.subs(par[0],val)) if par else g for g in Gs]
def rk(M): return M.rank(simplify=True)
def ns(M): return M.nullspace(simplify=True)
best=None
def maxiso(W):
    d=W.shape[1]
    if d==0: return 0
    random.seed(5); comb=sum((random.randint(1,97)*(W.T*g*W) for g in G),sp.zeros(d)); comb=comb.applyfunc(sp.expand); rho=rk(comb); return (d-rho)+rho//2
def dfs(W,m,path,depth):
    global best
    if m>maxiso(W): best=path; return True
    if depth==MAXD: return False
    cands=[]
    for i,g in enumerate(G):
        R=(W.T*g*W).applyfunc(sp.expand); r=rk(R)
        if r>=1: cands.append((-(r//2),-r,i,R))
    cands.sort(key=lambda c:(c[0],c[1]))
    for c in cands[:3]:
        _,_,i,R=c; r=rk(R); N=ns(R)
        W2=W*sp.Matrix.hstack(*N) if N else sp.zeros(W.shape[0],0)
        if dfs(W2,m-r//2,path+['B%d|r%d->dim%d,need%d'%(i,r,W2.shape[1],m-r//2)],depth+1): return True
    return False
ok=dfs(sp.eye(nq),4,[],0)
print('value',val,'=>','KILL via '+' > '.join(best) if ok else 'NOT decided within depth %d'%MAXD)
