import numpy as np, itertools, time, sys
from scipy.optimize import least_squares
# N2 plane-configuration problem, special position (beta-1): P_c = P_d != P_e. Planes P_0..P_4 = P_a,P_b,P_c,P_d,P_e (2x5, orthonormal rows); rho_a := row 0 of P_a,
# rho_b := row 0 of P_b.  Conditions (all rigorous necessary conditions of case N2):
#   (Q4)  P_a P_b P_k P_l = 0 in A_4 for {k,l} in {c,d,e};  (Qa) rho_a P_c P_d P_e = 0;  (Qb) rho_b P_c P_d P_e = 0;
#   all ten triple products P_i P_k P_l != 0  [equivalent to (NT) by (TV)]  -- imposed as hinge  ||P_i P_k P_l||_F >= DELTA.
P4=np.array(list(itertools.permutations(range(4)))); P3=np.array(list(itertools.permutations(range(3))))
ri=[];re=[];co=[]
for (k,l) in ((2,3),(2,4),(3,4)):
    for eps in itertools.product(range(2),repeat=4):
        for m in range(5): ri.append((0,1,k,l)); re.append(eps); co.append([c for c in range(5) if c!=m])
for first in (0,1):
    for eps in itertools.product(range(2),repeat=3):
        for m in range(5): ri.append((first,2,3,4)); re.append((0,)+eps); co.append([c for c in range(5) if c!=m])
RI=np.array(ri); RE=np.array(re); CO=np.array(co)
TRI=list(itertools.combinations(range(5),3)); K3=list(itertools.combinations(range(5),3))
ti=[];te=[];tc=[]
for T in TRI:
    for eps in itertools.product(range(2),repeat=3):
        for K in K3: ti.append(T); te.append(eps); tc.append(K)
TI=np.array(ti); TE=np.array(te); TC=np.array(tc)
def planes(x):
    B=(x[:40]+1j*x[40:]).reshape(4,2,5)          # P_a, P_b, P_c (= P_d), P_e
    return np.stack([B[0],B[1],B[2],B[2],B[3]])
def q4(A):
    Mx=A[RI[:,:,None],RE[:,:,None],CO[:,None,:]]
    return sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]]*Mx[:,3,p[3]] for p in P4)
def trip(A):
    Mx=A[TI[:,:,None],TE[:,:,None],TC[:,None,:]]
    v=sum(Mx[:,0,p[0]]*Mx[:,1,p[1]]*Mx[:,2,p[2]] for p in P3)
    return np.sqrt((np.abs(v.reshape(10,80))**2).sum(1))
DELTA=float(sys.argv[2]) if len(sys.argv)>2 else 0.25
CMIN=0.35; NVAN=int(sys.argv[4]) if len(sys.argv)>4 else 1
def res(x,w=3.0):
    A=planes(x); r=q4(A)
    G=np.einsum('iaj,ibj->iab',A,A.conj())-np.eye(2)[None]
    Pc=A[2].conj().T@A[2]; Pe=A[4].conj().T@A[4]; dsep=np.array([w*max(0,0.6-np.linalg.norm(Pc-Pe))])
    hinge=w*np.maximum(0,DELTA-trip(A))
    cn=np.sort(np.sqrt((np.abs(A)**2).sum(axis=(0,1))))
    h2=w*np.maximum(0,CMIN-cn[NVAN:])                 # all but the NVAN smallest columns have norm >= CMIN  (L156: at most one column vanishes on M)
    return np.concatenate([r.real,r.imag,G.real.ravel(),G.imag.ravel(),hinge,h2,dsep])
def rank(M,tol=1e-6):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(1,s[0])).sum())
if __name__=='__main__':
    rng=np.random.default_rng(int(sys.argv[1])); TL=float(sys.argv[3]) if len(sys.argv)>3 else 110
    t0=time.time(); nconv=0; best=[]; kinds={}; sols=[]
    for s in range(1000):
        if time.time()-t0>TL: break
        sol=least_squares(res,rng.normal(size=80)*0.6,method='lm',max_nfev=int(sys.argv[5]) if len(sys.argv)>5 else 1500)
        c=np.sqrt(2*sol.cost); best.append(c)
        if c<1e-8:
            nconv+=1; A=planes(sol.x); sols.append(sol.x)
            cn=np.sqrt((np.abs(A)**2).sum(axis=(0,1))); ncol=int((cn>1e-5).sum())
            ra=np.sort(np.abs(A[0,0]))[::-1]; rb=np.sort(np.abs(A[1,0]))[::-1]
            sa=int((ra>1e-5).sum()); sb=int((rb>1e-5).sum())
            par=abs(np.vdot(A[0,0],A[1,0]))
            dS=rank(np.vstack([A[2],A[3],A[4]])); dall=rank(A.reshape(10,5))
            inter=[4-rank(np.vstack([A[i],A[k]])) for i in range(5) for k in range(i)]
            key=('cols %d'%ncol,'|supp rho_a| %d'%sa,'|supp rho_b| %d'%sb,'rho_a||rho_b %d'%(par>1-1e-6),'dim(Pc+Pd+Pe) %d'%dS,'dim sum all %d'%dall,
                 '#meeting pairs %d'%sum(1 for t in inter if t>0))
            kinds[key]=kinds.get(key,0)+1
    print('NVAN',NVAN,'DELTA %.2f: starts %d, exact solutions %d  (%.0f s)'%(DELTA,s,nconv,time.time()-t0))
    if best: print('residual quantiles (min, 10%%, median): %.2e %.2e %.2e'%(min(best),np.quantile(best,0.1),np.median(best)))
    for k,v in sorted(kinds.items(),key=lambda t:-t[1]): print('  ',v,k)
    np.save('n2_planesB1_sols_%s_v%d.npy'%(sys.argv[1],NVAN),np.array(sols))
