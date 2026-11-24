# verify2 round 6: VF-A by linear algebra (numeric preview). T(N) = N + span(E1,E2); second-order equations restricted to a E1 + b E2.
import numpy as np, itertools
exec(open('/home/kevxhk/work/L-gct-210/verify2/vf/firstorder_A.py').read().split("EB=Ebasis()")[0])
P2=list(itertools.permutations(range(2)))
def hess_c(Y,E,Ep):
    """second derivative of c_j at Y in directions E, E' (bilinear): sum over (r,c),(r',c') E[r,c] E'[r',c'] perm_2(rest)"""
    U=1+Y; out=np.zeros(5,complex)
    for j in range(5):
        tot=0
        for r in range(4):
            for rp in range(4):
                if rp==r: continue
                rows=[x for x in range(4) if x not in (r,rp)]
                for c in range(5):
                    if c==j or E[r,c]==0: continue
                    for cp in range(5):
                        if cp in (j,c) or Ep[rp,cp]==0: continue
                        cols=[x for x in range(5) if x not in (j,c,cp)]; A=U[np.ix_(rows,cols)]
                        tot+=E[r,c]*Ep[rp,cp]*(A[0,0]*A[1,1]+A[0,1]*A[1,0])
        out[j]=tot
    return out
EB=Ebasis(); rng=np.random.default_rng(1)
for sb in (1,-1):
    for sx in (1,-1):
        beta=sb*np.sqrt(3)/4; xi=sx*np.sqrt(complex(-3/(32*beta)))
        Z=np.outer(one/4+beta*chi2,m)+np.outer(chi1,[0,xi,-xi,0,0]); Zs=np.outer(chi1,mbar)
        pts=[rng.normal(size=2)+1j*rng.normal(size=2) for _ in range(14)]
        A=np.concatenate([Wm@np.einsum('jrc,nrc->jn',grad_c(k*Z+t*Zs),EB) for k,t in pts])
        u,s,vh=np.linalg.svd(A); rk=int(np.sum(s>1e-9*s[0])); T=vh[rk:].conj()                 # coefficient vectors (4,16)
        TE=np.einsum('an,nrc->arc',T,EB)                                                       # (4,4,5) matrices spanning T(N)
        # complement of N in T(N)
        Nm=np.array([Z.ravel(),Zs.ravel()]); TEf=TE.reshape(len(TE),20)
        # project out N (any complement): solve TEf = coef @ basis; pick two vectors of T(N) independent mod N
        Mx=np.concatenate([Nm,TEf]); uu,ss,vv=np.linalg.svd(Mx); assert int(np.sum(ss>1e-9*ss[0]))==4
        Q,_=np.linalg.qr(Nm.T); comp=TEf-(TEf@Q.conj())@Q.T; uu,ss,vv=np.linalg.svd(comp); E12=vv[:2].reshape(2,4,5)
        # check E12 in T(N) (first order) 
        chk=max(np.abs(Wm@np.einsum('jrc,rc->j',grad_c(k*Z+t*Zs),E)).max() for k,t in pts for E in E12)
        rows=[]
        for k,t in pts:
            Y0=k*Z+t*Zs
            h11=Wm@hess_c(Y0,E12[0],E12[0]); h12=Wm@hess_c(Y0,E12[0],E12[1]); h22=Wm@hess_c(Y0,E12[1],E12[1])
            rows.append(np.stack([h11,2*h12,h22],axis=1))            # (4,3): coefficients of a^2, ab, b^2
        M2=np.concatenate(rows); s2=np.linalg.svd(M2,compute_uv=False)
        print('beta %+d xi %+d: dim T(N) = %d (first-order check on E1,E2: %.1e); binary quadrics from the x^2-coefficients: singular values %s -> rank %d'%(sb,sx,16-rk,chk,np.array2string(s2,precision=3),int(np.sum(s2>1e-9*s2[0]))))
