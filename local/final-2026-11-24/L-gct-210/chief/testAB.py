import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief')
from core import *
rng=np.random.default_rng(5)
def hat(B):
    return np.concatenate([np.ones((1,5,5),complex),B])   # index 0 = J ; ell = coefficient of J
def sub_with_zero(Bh,cells):
    # coefficients c with sum c_k Bh[k][cell]=0 on cells
    A=np.array([[Bh[k][i,j] for k in range(len(Bh))] for (i,j) in cells])
    return nullspace(A)   # columns = coefficient vectors
def Bmat(x,rows):
    Bm=np.zeros((5,5),complex)
    for j in range(5):
        for l in range(5):
            if j!=l:
                T=[c for c in range(5) if c not in (j,l)]
                Bm[j,l]=perm(x[np.ix_(rows,T)])
    return Bm
def rank(A,tol=1e-8):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int(np.sum(s>tol*max(1,s[0]))) if len(s) else 0
for name,f in SP.items():
    B=f(); Bh=hat(B); l=len(B)
    worstA=0; okB=True; statsA=[]; statsB={}
    for r,rp in itertools.combinations(range(5),2):
        abc=[i for i in range(5) if i not in (r,rp)]
        # Theorem A
        N=sub_with_zero(B,[(i,j) for i in (r,rp) for j in range(5)])   # L_{rr'}
        lam=N.shape[1]
        proj=np.array([np.concatenate([b[r],b[rp]]) for b in Bh])  # rows of hat projected
        p1=rank(proj)
        maxrk=0
        for _ in range(3 if lam else 0):
            c=N@(rng.normal(size=lam)+1j*rng.normal(size=lam)); x=np.tensordot(c,B,1)
            Bx=Bmat(x,abc); rk=rank(Bx); maxrk=max(maxrk,rk)
            # isotropy of I^ : u^T Bx v for (u,v) in proj span
            G=np.array([[proj[a][:5]@Bx@proj[b][5:]+proj[b][:5]@Bx@proj[a][5:] for b in range(len(proj))] for a in range(len(proj))])
            worstA=max(worstA,np.abs(G).max())
            assert p1<=10-rk, (name,r,rp,p1,rk)
        statsA.append((r,rp,lam,p1-1,maxrk))
        # Theorem B
        for T in itertools.combinations(range(5),2):
            Tc=[c for c in range(5) if c not in T]
            U=sub_with_zero(Bh,[(i,j) for i in (r,rp) for j in Tc])
            dU=U.shape[1]
            ellU=U[0,:]   # ell on U basis
            inL=np.abs(ellU).max()<1e-9
            # Pi = projection to 2x2 block
            Pi=np.array([[sum(U[k,a]*Bh[k][i,j] for k in range(len(Bh))) for a in range(dU)] for i in (r,rp) for j in T])  # 4 x dU
            dPi=rank(Pi) if dU else 0
            # gram of q on U basis: q(z)=z11 z22+z12 z21
            Qf=np.array([[0,0,0,1],[0,0,1,0],[0,1,0,0],[1,0,0,0]],complex)
            G=Pi.T@Qf@Pi if dU else np.zeros((0,0))
            rq=rank(G) if dU else 0
            # f identically zero on U?
            fz=True
            for _ in range(4 if dU else 0):
                c=U@(rng.normal(size=dU)+1j*rng.normal(size=dU)); u=np.tensordot(c,Bh,1)
                if abs(perm(u[np.ix_(abc,Tc)]))>1e-8: fz=False
                # check perm = 120 ell^5
                assert abs(perm(u)-120*c[0]**5)<1e-7*(1+abs(c[0])**5)
            typ=('B1' if (not inL) else ('q0' if rq==0 else ('B2' if fz else 'VIOL')))
            if not inL and rq>1: typ='VIOL'
            if typ=='VIOL': okB=False
            key=(typ,dU,dPi,rq)
            statsB[key]=statsB.get(key,0)+1
    print(name,'dim',l,'ThmA isotropy err %.1e'%worstA,'ThmB ok',okB)
    print('   A (r,r\',lam,p,maxrankB):',statsA)
    print('   B (type,dimU,dimPi,rank q): count',statsB)
