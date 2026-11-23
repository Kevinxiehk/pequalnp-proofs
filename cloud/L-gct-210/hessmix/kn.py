import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/hessmix')
from hk import *
from nya import Phi, nullsp, RowS, ColS
def span(M):
    M=np.atleast_2d(M); return np.linalg.svd(M)[2][:rank(M)] if len(M) else M
def stab(P):
    # z with z*p in span(P) for all p in P: linear in z (25 unknowns)
    Pb=span(P); Nperp=nullsp(Pb)  # rows orthogonal (dot) complement: x in span(P) iff Nperp.conj()?? use bilinear: span(P) = {x: N x = 0} with N = nullsp(Pb.conj())
    N=nullsp(Pb.conj()).conj()  # N @ x = 0 iff x in span(P)  (hermitian complement)
    rows=[]
    for p in Pb:
        rows.append(N@np.diag(p))   # N (z*p) = 0
    A=np.vstack(rows) if len(N) else np.zeros((1,25))
    return 25-rank(A)
ex=examples()
for name,B in ex.items():
    Bo=orth(B); l=len(Bo); Y=np.array([Phi(b).ravel() for b in Bo])
    C=Y@ColS.T; R=Y@RowS.T; rA=rank(R); rB=rank(C)
    YA=span(nullsp(C.T)@Y) if rB<l else np.zeros((0,25)); YB=span(nullsp(R.T)@Y) if rA<l else np.zeros((0,25))
    P=np.array([a*b for a in YA for b in YB]); dP=rank(P); h=stab(P)
    GY=np.array([ (y.reshape(5,5)-(5/9)*(y.reshape(5,5).sum(1)[:,None]+y.reshape(5,5).sum(0)[None,:])).ravel() for y in Y])
    CG=np.vstack([np.ones((1,25)),GY]); j=rank(CG)+dP-rank(np.vstack([CG,P]))
    orthG=np.abs(GY@Y.T).max()
    print(name,'l=%d rA=%d rB=%d d=%d | dimYA=%d dimYB=%d dim(YA*YB)=%d h=%d (Kneser lb %d) j=%d | 4l=%d <= 24+rA+rB+h+j=%d   [GY.Y %.0e]'%(
        l,rA,rB,inv(B)['d'],len(YA),len(YB),dP,h,len(YA)+len(YB)-h,j,4*l,24+rA+rB+h+j,orthG))
