import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
from s3lib import *
from test_lemmas import spaces
# Corollary of (O5): K = {r,r'} x T^c (2x3) not ell-supporting  =>  dim{t in L: t[rr';T^c] = 0} <= 3 + m^T,
# and the image of that space in the 3x3 block [abc;T^c] has dim <= 3 and consists of lineality directions of perm_3 at b_T.
rng=np.random.default_rng(4)
tot=0; viol=0; mx=0; stats={}
for name,B in spaces():
    Bh=hat(B)
    for rr in PAIRS:
        abc=[i for i in R5 if i not in rr]
        for T in PAIRS:
            Tc=[c for c in R5 if c not in T]; K=[(i,j) for i in rr for j in Tc]
            if ell_supporting(B,K): continue
            U=elems(B,sub_zero(B,K)); mT=len(XS(B,cols=Tc)); tot+=1
            img=rank(np.array([u[np.ix_(abc,Tc)].reshape(-1) for u in U])) if len(U) else 0
            stats[(len(U),mT,img)]=stats.get((len(U),mT,img),0)+1
            if len(U)>3+mT or img>3: viol+=1
            # lineality check at a base point with ell = 1
            C=sub_zero(Bh,K); Uh=elems(Bh,C)
            c=rng.normal(size=len(Uh))+1j*rng.normal(size=len(Uh)); u0=np.tensordot(c,Uh,1); l0=(C@c)[0]
            if len(U):
                x=np.tensordot(rng.normal(size=len(U))+1j*rng.normal(size=len(U)),U,1)
                p0=perm(u0[np.ix_(abc,Tc)]); p1=perm((u0+x)[np.ix_(abc,Tc)])
                if abs(p0-p1)>1e-7*max(1,abs(p0)): viol+=1
print('B1 2x3 blocks tested:',tot,' violations:',viol)
print('(dim{t in L: t[rr\';T^c]=0}, m^T, dim image in 3x3 block): count'); 
for k,v in sorted(stats.items()): print('  ',k,v)
