# Round 11, target 1: LOCAL test.  For a census space M with a 3-dim row block of rank 2 (rows (r,j): kernel line l = e_r w0, W = X_0, n spans
# W^perp cap 1^perp), fix l' = l + eps e_j n (this would make rank B = 3) and let the other five basis elements move (Gauss-Newton from M) to
# restore levelness.  Small residual for small eps => nearby rank-3 blocks exist.  Controls: 'triv' (l' = l + eps*(another element of M), always
# solvable) and 'rand' (a random sum-zero direction in row j).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from ext6 import F45
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj()
f=sys.argv[1]; r=int(sys.argv[2]); j=int(sys.argv[3])
M=np.load(f); M=M/np.abs(M).max()
mr=np.zeros((4,5),bool); mr[r]=True; Lr=sub_supported(M,mr); assert len(Lr)==1, len(Lr)
l=Lr[0]/np.linalg.norm(Lr[0])
mask=mr.copy(); mask[j]=True; P=sub_supported(M,mask)
Pf=P.reshape(len(P),-1); Rest=Pf-np.outer(Pf@l.ravel().conj(),l.ravel()); u,s,vh=np.linalg.svd(Rest); Rest=vh[:int((s>1e-7).sum())].reshape(-1,4,5)
sv=Rest[:,r,:].sum(1); c0=null(sv[None,:],1e-6) if np.abs(sv).max()>1e-6 else np.eye(len(Rest)); R0=np.einsum('kc,cab->kab',c0,Rest)
W=np.concatenate([l[r][None,:],R0[:,r,:]],0); W=np.linalg.svd(W)[2][:3]           # row space (3-dim)
assert np.linalg.matrix_rank(np.concatenate([l[r][None,:],R0[:,r,:]],0),tol=1e-6)==3
n=null(np.concatenate([W.conj(),np.ones((1,5))],0)); assert len(n)==1; n=n[0]      # bilinear: <W,n> = 0 uses W.conj() rows? (W rows complex)
n=null(np.concatenate([W,np.ones((1,5))],0).conj())[0].conj()
assert np.abs(W@n).max()<1e-8 and abs(n.sum())<1e-8
Mf=M.reshape(6,-1); Q=Mf-np.outer(Mf@l.ravel().conj(),l.ravel()); u,s,vh=np.linalg.svd(Q); Oth=vh[:5].reshape(5,4,5)
rg=np.random.default_rng(1); C=rg.normal(size=(120,6))+1j*rg.normal(size=(120,6))
def run(dirn,eps):
    lp=l.copy(); lp=lp+eps*dirn
    def res(x):
        E=np.concatenate([lp[None],Oth+x.reshape(5,4,5)],0); return F45(np.einsum('nk,kij->nij',C,E))-120
    x=np.zeros(100,complex); rr=res(x); c=np.linalg.norm(rr)
    for it in range(40):
        J=np.empty((len(rr),100),complex)
        for k in range(100):
            xp=x.copy(); xp[k]+=1e-7; J[:,k]=(res(xp)-rr)/1e-7
        lam=1e-6*np.abs(J).max()**2; dx=np.linalg.solve(J.conj().T@J+lam*np.eye(100),-J.conj().T@rr); xn=x+dx; rn=res(xn)
        if np.linalg.norm(rn)<c: x,rr,c=xn,rn,np.linalg.norm(rn)
        else:
            xn=x+0.25*dx; rn=res(xn)
            if np.linalg.norm(rn)<c: x,rr,c=xn,rn,np.linalg.norm(rn)
            else: break
        if c<1e-12: break
    return c,np.linalg.norm(x)
dn=np.zeros((4,5),complex); dn[j]=n/np.linalg.norm(n)
dt=Oth[0]/np.linalg.norm(Oth[0])
v=rg.normal(size=5)+1j*rg.normal(size=5); v-=v.mean(); dr=np.zeros((4,5),complex); dr[j]=v/np.linalg.norm(v)
print(f,'rows',(r,j),' n =',np.round(n/np.abs(n).max(),3))
for name,d in (('n (rank 3)',dn),('triv',dt),('rand',dr)):
    print('  %-11s'%name,'  '.join('eps %.0e: res %.1e (|dx| %.1e)'%((e,)+run(d,e)) for e in (1e-3,1e-2,1e-1)),flush=True)
