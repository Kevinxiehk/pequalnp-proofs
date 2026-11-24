import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
from s3lib import *
import glob
rng=np.random.default_rng(11)
TOL=1e-7
def rnd(A):
    c=rng.normal(size=len(A))+1j*rng.normal(size=len(A)); return np.tensordot(c,A,1)
def spaces():
    for k,f in SP.items(): yield k,f()
    # rows' free-line-free 7-dim spaces (defect construction), if loadable
    try:
        sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
        import build7
        for fn in sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d4_defect1_s*.npy'))[:3]+sorted(glob.glob('/home/kevxhk/work/L-gct-210/rows/clm_p4_d5_defect2_s*.npy'))[:2]:
            Z=np.load(fn); B,e=build7.build(Z); 
            if build7.check(B)<1e-7: yield fn.split('/')[-1],B
    except Exception as ex: print('rows spaces not loaded:',ex)
def transpose(B): return np.array([b.T for b in B])
def test_D2(B):
    """2-row elements x in Y_ab: q_T(x)!=0 => block cde x T ell-supporting and f_T==0 on U_K (U_K in L)"""
    n=0; viol=0; nq=0
    for ab in PAIRS:
        S=[r for r in R5 if r not in ab]; Y=XS(B,rows=S)
        if len(Y)==0: continue
        for _ in range(3):
            x=rnd(Y)
            for T in PAIRS:
                q=x[ab[0],T[0]]*x[ab[1],T[1]]+x[ab[0],T[1]]*x[ab[1],T[0]]; n+=1
                if abs(q)>TOL:
                    nq+=1; K=[(i,j) for i in S for j in T]
                    if not ell_supporting(B,K): viol+=1; continue
                    U=elems(B,sub_zero(B,K)); Tc=[c for c in R5 if c not in T]
                    for _ in range(3):
                        u=rnd(U)
                        if abs(perm(u[np.ix_(S,Tc)]))>TOL: viol+=1
    return n,nq,viol
def test_SR(B):
    """single-row e_a w^T in L, w_j!=0 => 4x1 block (rows != a) x {j} ell-supporting, and perm_4(u^(aj))=0 on L^j"""
    n=0; viol=0
    for a in R5:
        Z=XS(B,rows=[r for r in R5 if r!=a])
        if len(Z)==0: continue
        x=rnd(Z)
        for j in R5:
            if abs(x[a,j])>TOL:
                n+=1; K=[(i,j) for i in R5 if i!=a]
                if not ell_supporting(B,K): viol+=1
                Lj=XS(B,cols=[j])
                if len(Lj):
                    for _ in range(3):
                        u=rnd(Lj); m=np.delete(np.delete(u,a,0),j,1)
                        if abs(perm(m))>TOL: viol+=1
    return n,viol
def test_GZ(B):
    """sub-FK block K=SxZ (|S|+|Z|=5) not ell-supporting: f1 = k ell^|S|, f2 = k' ell^(5-|S|) on U_K; f_i(u+x)=f_i(u) for x in U_K cap L"""
    Bh=hat(B); n=0; viol=0
    for p in (1,2,3,4):
        for S in itertools.combinations(R5,p):
            Sc=[i for i in R5 if i not in S]
            for Z in itertools.combinations(R5,5-p):
                Zc=[j for j in R5 if j not in Z]; K=[(i,j) for i in S for j in Z]
                if ell_supporting(B,K): continue
                C=sub_zero(Bh,K); U=elems(Bh,C)
                if len(U)<2: continue
                n+=1
                # ell coordinate = coefficient of J = C[0,:]
                vals=[]
                for _ in range(3):
                    c=rng.normal(size=len(U))+1j*rng.normal(size=len(U)); u=np.tensordot(c,U,1); l=(C@c)[0]
                    f1=perm(u[np.ix_(S,Zc)]); f2=perm(u[np.ix_(Sc,Z)])
                    vals.append((f1/l**p, f2/l**(5-p)))
                v=np.array(vals)
                if np.abs(v-v[0]).max()>1e-5*max(1,np.abs(v).max()): viol+=1
    return n,viol
def test_S12(B):
    """x in Y_ab, u in L^: perm[x_a;x_b;u_c;u_d;u_e]=0 and perm[x_a;u_b;..]+perm[u_a;x_b;..]=0"""
    Bh=hat(B); n=0; viol=0
    for ab in PAIRS:
        S=[r for r in R5 if r not in ab]; Y=XS(B,rows=S)
        if len(Y)==0: continue
        for _ in range(2):
            x=rnd(Y); u=rnd(Bh); n+=1
            m=u.copy(); m[ab[0]]=x[ab[0]]; m[ab[1]]=x[ab[1]]
            m1=u.copy(); m1[ab[0]]=x[ab[0]]; m2=u.copy(); m2[ab[1]]=x[ab[1]]
            if abs(perm(m))>1e-6 or abs(perm(m1)+perm(m2))>1e-6: viol+=1
    return n,viol
for name,B in spaces():
    print(name,'dim',len(B),'level err %.1e'%levelerr(B,rng))
    print('   D2 rows  (cases, q!=0, viol):',test_D2(B),'  cols:',test_D2(transpose(B)))
    print('   SR rows  (cases, viol):',test_SR(B),'  SC cols:',test_SR(transpose(B)))
    print('   GZ (non-ell-supp sub-FK blocks with dim U>=2, viol):',test_GZ(B))
    print('   S1/S2 (cases, viol):',test_S12(B))
