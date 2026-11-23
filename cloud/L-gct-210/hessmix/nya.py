import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
def Phi(x):
    m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
def nullsp(M,tol=1e-9):
    M=np.atleast_2d(M); u,s,vh=np.linalg.svd(M); rk=int((s>tol*max(1,s[0] if len(s) else 1)).sum()); return vh[rk:].conj()
RowS=np.kron(np.eye(5),np.ones((1,5))); ColS=np.kron(np.ones((1,5)),np.eye(5))
def analyse(YA,label):
    # YA rows in C^25 (u coords), column sums zero
    P=np.array([a*b for i,a in enumerate(YA) for b in YA[i:]])
    F=np.vstack([RowS,YA,P])  # Y_B must be orthogonal (dot) to these
    N=nullsp(F)  # basis of N(Y_A) (rows), dot-orthogonal complement
    n=len(N)
    qB=N@N.T-(5/9)*(N@ColS.T)@(ColS@N.T)
    rq=rank(qB)
    forms=[N@np.diag(a)@N.T for a in YA]
    rd=[rank(f) for f in forms]
    # generic pencil member
    rng=np.random.default_rng(0); c=rng.normal(size=len(YA)+1)
    pen=c[0]*qB+sum(ci*f for ci,f in zip(c[1:],forms)); rp=rank(pen)
    print(label,'dim Rows+YA+YA*YA =',rank(F),' dim N(YA) =',n,' rank qB|N =',rq,' ranks diag(a)|N:',rd,' generic pencil rank',rp,
          ' => max isotropic for qB alone:',(n-rq)+rq//2, flush=True)
    return N
if __name__=='__main__':
    ex=examples()
    for name in ['L080','ex1','ex2']:
        Bo=orth(ex[name]); Y=np.array([Phi(b).ravel() for b in Bo])
        C=Y@ColS.T; R=Y@RowS.T
        YA=nullsp(C.T)@Y; YA=np.linalg.svd(YA)[2][:rank(YA)]
        YB=nullsp(R.T)@Y; YB=np.linalg.svd(YB)[2][:rank(YB)]
        print(name,'dim YA',len(YA),'rank R on YA',rank(YA@RowS.T),' dim YB',len(YB),'rank C on YB',rank(YB@ColS.T))
        analyse(YA,name+' N(YA):')
        # symmetric: N(YB) for YA (transpose roles)
        YBt=np.array([y.reshape(5,5).T.ravel() for y in YB])
        analyse(YBt,name+' N(YB) [transposed]:')
