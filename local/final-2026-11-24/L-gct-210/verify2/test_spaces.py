# verify2: tests of the foundation statements on known level spaces (my own implementation).
import numpy as np, itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/verify2')
from vlib import *
rng=np.random.default_rng(7)
S=spaces(); TOL=1e-7
tot={}
def add(k,ok): 
    a=tot.setdefault(k,[0,0]); a[0]+=1; a[1]+=0 if ok else 1
for name,B in S.items():
    d=len(B); H=hat(B)
    # level check
    err=max(abs(perm(J+np.tensordot(rnd(rng,d),B,1))-120) for _ in range(3))
    # R0: perm = 120 ell^5 on L^
    for _ in range(3):
        c=rnd(rng,d+1); u=(c@H).reshape(5,5); add('R0',abs(perm(u)-120*c[0]**5)<TOL*max(1,abs(c[0])**5))
    for tr in (False,True):
        Bt=np.array([M.T for M in B]) if tr else B; Ht=hat(Bt)
        # general ZBF: all blocks S x Z with |S|+|Z|=5
        for s in range(1,5):
            for Sr in itertools.combinations(range(5),s):
                for Z in itertools.combinations(range(5),5-s):
                    Zc=[j for j in range(5) if j not in Z]; Sc=[i for i in range(5) if i not in Sr]
                    N=subspace(Ht,[(i,j) for i in Sr for j in Z])   # columns: coefficient vectors of U_K
                    if N.shape[1]==0: continue
                    ellnz=np.linalg.norm(N[0,:])>1e-8
                    pts=[N@rnd(rng,N.shape[1]) for _ in range(4)]
                    us=[(c@Ht).reshape(5,5) for c in pts]
                    f1=[perm(u[np.ix_(Sr,Zc)]) for u in us]; f2=[perm(u[np.ix_(Sc,Z)]) for u in us]
                    if ellnz:
                        k1=[f1[i]/pts[i][0]**s for i in range(4)]; k2=[f2[i]/pts[i][0]**(5-s) for i in range(4)]
                        ok=max(abs(k-k1[0]) for k in k1)<TOL*max(1,abs(k1[0])) and max(abs(k-k2[0]) for k in k2)<TOL*max(1,abs(k2[0])) and abs(k1[0]*k2[0]-120)<1e-6
                        add('ZBF ell!=0: f1=k ell^s, f2=k\' ell^(5-s), kk\'=120',ok)
                    else:
                        ok=max(abs(x) for x in f1)<TOL or max(abs(x) for x in f2)<TOL
                        add('ZBF ell=0: f1=0 or f2=0 on U',ok)
        # ThB (dim Pi_T<=2 in B1), N3'-L, ThA
        for r,r2 in itertools.combinations(range(5),2):
            oth=[i for i in range(5) if i not in (r,r2)]
            X=subspace(Ht,[(i,j) for i in (r,r2) for j in range(5)])   # = L_{rr'} (ell=0 automatically)
            lam=X.shape[1]
            add('zero rows => ell=0',lam==0 or np.linalg.norm(X[0,:])<1e-8)
            for T in itertools.combinations(range(5),2):
                Tc=[j for j in range(5) if j not in T]
                N=subspace(Ht,[(i,j) for i in (r,r2) for j in Tc])
                if np.linalg.norm(N[0,:])>1e-8:   # B1
                    dimPi=N.shape[1]-lam
                    add('ThB: B1 => dim Pi_T<=2',dimPi<=2)
                    # N3'-L: dim{t in L: t[rr';T^c]=0} <= 3 + m^T
                    NL=N.shape[1]-1
                    mT=subspace(Ht[1:],[(i,j) for i in range(5) for j in Tc]).shape[1]
                    add("N3'-L: dim{t in L: t[rr';T^c]=0} <= 3+m^T",NL<=3+mT)
            # ThA
            for _ in range(2):
                if lam==0: break
                x=((X@rnd(rng,lam))@Ht).reshape(5,5)
                Bx=np.zeros((5,5),complex)
                for j,l in itertools.combinations(range(5),2):
                    cols=[c for c in range(5) if c not in (j,l)]; Bx[j,l]=Bx[l,j]=perm(x[np.ix_(oth,cols)])
                for _ in range(3):
                    t=np.tensordot(rnd(rng,d),Bt,1)
                    val=(1+t[r])@Bx@(1+t[r2]); add('ThA: (1+t_r)^T B_x (1+t_r\')=0',abs(val)<TOL*max(1,np.abs(Bx).max()))
                # rank bound dim pi_{rr'}(L) <= 9 - rank B_x
                p=rk(Bt[:,[r,r2],:].reshape(d,10)); add('ThA: dim pi_rr\'(L) <= 9 - rank B_x',p<=9-rk(Bx) if np.abs(Bx).max()>1e-9 else True)
        # CA2 general form: xi in L_e, G(xi) in pi_e(L^)^perp ; if a_e=1 then G(xi)=0
        for e in range(5):
            oth=[i for i in range(5) if i!=e]
            Xe=subspace(Ht[1:],[(e,j) for j in range(5)])
            if Xe.shape[1]==0: continue
            ae=5-rk(Bt[:,e,:])
            Pe=Ht[:,5*e:5*e+5]   # rows span pi_e(L^)
            for _ in range(2):
                xi=((Xe@rnd(rng,Xe.shape[1]))@Ht[1:]).reshape(5,5)
                G=np.array([perm(xi[np.ix_(oth,[c for c in range(5) if c!=m])]) for m in range(5)])
                add('CA2: G(xi) perp pi_e(L^)',np.abs(Pe@G).max()<TOL*max(1,np.abs(G).max()))
                if ae==1: add('CA2: a_e=1 => G(xi)=0',np.abs(G).max()<TOL)
    print('%-14s dim %d level err %.1e'%(name,d,err))
for k,(n,bad) in tot.items(): print('%-60s cases %6d violations %d'%(k,n,bad))
