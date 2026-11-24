# which equation blocks are needed for r=8 infeasibility (u-coords).  blocks: QAA QAB QBB TAAA TAAB TABB TBBB
import sys, time; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
from scipy.optimize import least_squares
sys.path.insert(0,'/home/kevxhk/work/L-gct-086/smallcases')
from level import dc_basis
use=set(sys.argv[1].split(',')); seed=int(sys.argv[2]); ns=int(sys.argv[3])
rng=np.random.default_rng(seed)
Ub=np.linalg.qr(dc_basis(5).reshape(16,-1).T)[0].T
RowS=np.kron(np.eye(5),np.ones((1,5))); ColS=np.kron(np.ones((1,5)),np.eye(5))
E4=np.array([np.eye(5)[k]-np.eye(5)[4] for k in range(4)])
A0=np.array([np.outer(E4[k],np.ones(5)).ravel()/5 for k in range(4)]); B0=np.array([np.outer(np.ones(5),E4[k]).ravel()/5 for k in range(4)])
lab=['A']*4+['B']*4
def build(x):
    z=x[:len(x)//2]+1j*x[len(x)//2:]; G=z[:64].reshape(16,4); H=z[64:].reshape(16,4)
    return np.vstack([A0+G.T@Ub,B0+H.T@Ub])
blocks2={};blocks3={}
for a in range(8):
    for b in range(a,8):
        key='Q'+''.join(sorted(lab[a]+lab[b])); blocks2.setdefault(key,[]).append((a,b))
        for c in range(b,8):
            key3='T'+''.join(sorted(lab[a]+lab[b]+lab[c])); blocks3.setdefault(key3,[]).append((a,b,c))
def res(x):
    Y=build(x); R=Y@RowS.T; C=Y@ColS.T
    E2=Y@Y.T-(5/9)*(R@R.T+C@C.T)
    T=np.einsum('ap,bp,cp->abc',Y,Y,Y)-(1/9)*(np.einsum('ap,bp,cp->abc',R,R,R)+np.einsum('ap,bp,cp->abc',C,C,C))
    out=[]
    for k,v in blocks2.items():
        if k in use: out.append(np.array([E2[a,b] for a,b in v]))
    for k,v in blocks3.items():
        if k in use: out.append(np.array([T[a,b,c] for a,b,c in v]))
    o=np.concatenate(out); o=np.concatenate([o.real,o.imag]); return np.concatenate([o,np.zeros(max(0,256-len(o)))])
best=[]
for st in range(ns):
    r=least_squares(res,0.5*rng.normal(size=256),method='lm',max_nfev=4000,xtol=1e-15,ftol=1e-15,gtol=1e-15)
    best.append(np.linalg.norm(r.fun))
print(sorted(use),'residuals:',' '.join('%.1e'%b for b in best),flush=True)
