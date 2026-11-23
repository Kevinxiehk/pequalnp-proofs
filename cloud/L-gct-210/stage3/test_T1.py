import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
from s3lib import *
from test_lemmas import spaces, rnd
import io, contextlib
def G4(rows):
    """five 4x4 maximal-minor permanents of a 4x5 matrix"""
    M=np.array(rows); return np.array([perm(np.delete(M,m,1)) for m in R5])
def rowproj(X,i): 
    if len(X)==0: return np.zeros((0,5),complex)
    A=np.array([x[i] for x in X]); u,s,vh=np.linalg.svd(A); r=int(np.sum(s>1e-8)); return vh[:r]
tot=0; viol=0; info=[]
for name,B in spaces():
    a=[5-projdim(B,[(r,j) for j in R5]) for r in R5]
    for e in R5:
        if a[e]!=1: continue
        Le=XS(B,rows=[e])
        for ab in PAIRS:
            if e in ab: continue
            c,d=[r for r in R5 if r not in ab and r!=e]
            Y=XS(B,rows=[c,d,e])
            if len(Y)==0: continue
            Rc=rowproj(XS(B,rows=[d,e]),c); Rd=rowproj(XS(B,rows=[c,e]),d)
            for _ in range(3):
                x=rnd(Y); xi=rnd(Le); tot+=1
                # (CA2) and s^2-coefficient on L_e
                if np.abs(G4([xi[i] for i in R5 if i!=e])).max()>1e-7: viol+=1
                if np.abs(G4([x[ab[0]],x[ab[1]],xi[c],xi[d]])).max()>1e-7: viol+=1
                if len(Rc) and len(Rd):
                    v=rnd(Rc); vp=rnd(Rd)
                    if np.abs(G4([x[ab[0]],x[ab[1]],v,vp])).max()>1e-7: viol+=1
            info.append((name[:22],e,ab,len(Y),len(Rc),len(Rd)))
print('T1 tests:',tot,'violations:',viol)
for i in info[:40]: print('  ',i)
