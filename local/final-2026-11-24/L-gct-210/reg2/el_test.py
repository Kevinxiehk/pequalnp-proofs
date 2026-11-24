# Test of EL-SAT: for a "saturated deletable-row space" M_S = S (+) e_i (x) U_S, S a level 4x5 space with row i = 0 and
# U_S := (C(S) + C1)^perp (rows' defect construction; C(S) = defect span of S), is Omega(M_S) inside A(U_S) = {s : U_S o s in U_S + C1}?
# S runs over random subspaces of M_i := M cap {row i = 0} for known level spaces M (6-dim exact families).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, pk
from a5 import onb
from a6 import T1
from autest_lib import AU, inside
rg=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
def defect_span(B,n=40):
    V=[]
    for _ in range(n):
        c=rg.normal(size=len(B))+1j*rg.normal(size=len(B)); Y=np.einsum('k,kab->ab',c,B)
        N=np.array([perm(np.delete(np.ones((4,5))+Y,j,axis=1)) for j in range(5)]); V.append(N-24)
    V=np.array(V); u,s,vh=np.linalg.svd(V); r=int((s>1e-8*max(s[0],1e-300)).sum()) if s[0]>1e-9 else 0
    return vh[:r]                           # rows span C(S) (row space of V)
def saturate(S,i):
    C=defect_span(S); A=np.concatenate([C,np.ones((1,5))],0) if len(C) else np.ones((1,5))
    U=null(A)                                # rows u with A u = 0 (bilinear)
    E=[]
    for u in U:
        m=np.zeros((4,5),complex); m[i]=u; E.append(m)
    return onb(np.concatenate([S,np.array(E)],0)) if len(E) else S, U
def omega(B):
    T=T1(embed(B),rg,npts=200); U_,Sv,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((Sv>1e-7*Sv[0]).sum()); return U_[:,:r].T,len(T)
def run(name,B,i):
    Mi=rowpart(B,[k for k in range(4) if k!=i])       # elements with row i zero
    print('== %s: dim %d, row %d, dim M_i = %d'%(name,len(B),i,len(Mi)),flush=True)
    for d in range(1,len(Mi)+1):
        for trial in range(2 if d<len(Mi) else 1):
            C=rg.normal(size=(d,len(Mi)))+1j*rg.normal(size=(d,len(Mi))); S=onb(np.einsum('kc,cab->kab',C,Mi))
            MS,U=saturate(S,i); le=level_err(MS,ntest=15)
            Om,nT=omega(MS); A=AU(U) if len(U) else np.eye(5,dtype=complex); ok=inside(Om,A)
            print('  dim S %d: e(S)=%d dim U=%d dim M_S=%d lev %.0e | dim T1 %d dim Omega %d dim A(U) %d  %s'%(d,5-1-len(U),len(U),len(MS),le,nT,len(Om),len(A),'OK' if ok else 'EL-SAT VIOLATED'),flush=True)
if __name__=='__main__':
    from dr211b_num import fam as fam2, member_g
    a,b,c=member_g(rg); run('(2,1,1|2)(ii) generic',onb(fam2(a,b,c)),0)
    b=np.array([1,-1,0,0],complex); c=np.array([1,1,-2,0],complex); from dr211b_num import cross4; run('(2,1,1|2)(ii) Sigma_4',onb(fam2(cross4(b,c),b,c)),0)
    from dr22_num_lib import fam22
    run('(2,2|2) generic',onb(fam22(0.3+0.2j,-1.1)),1)
    from p312_lib import fam as fam312
    run('(3,1|2) iso',onb(fam312(np.array([1,1j,-1,-1j,0]))),0)
    run('Mstar2',onb(np.load('/home/kevxhk/work/L-gct-210/reg2/Mstar2.npy')),3)
