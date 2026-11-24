"""EXACT check in Z[w] (w^2 = -1 - w) of the 'second kind' 7-dim level space:
   u(e_0-e_3)^T, ubar e_1^T, ubar e_4^T  (u = (1,w,w^2) on rows 0,1,3; ubar = (1,w^2,w)),  (1,1,-3,1,0)^T e_2^T,
   e_4 w^T with w_0 = w_3, sum w = 0 (3-dim)."""
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/rows')
from exact7 import level_identity
class W:
    __slots__=('a','b')
    def __init__(s,a=0,b=0): s.a=a; s.b=b
    def __add__(s,o):
        o=o if isinstance(o,W) else W(o); return W(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __mul__(s,o):
        o=o if isinstance(o,W) else W(o)
        # (a+bw)(c+dw) = ac + (ad+bc)w + bd w^2 = (ac - bd) + (ad + bc - bd) w
        return W(s.a*o.a-s.b*o.b, s.a*o.b+s.b*o.a-s.b*o.b)
    __rmul__=__mul__
    def __eq__(s,o):
        o=o if isinstance(o,W) else W(o); return s.a==o.a and s.b==o.b
    def __ne__(s,o): return not s.__eq__(o)
    def __repr__(s): return '(%d%+dw)'%(s.a,s.b)
one=W(1); w=W(0,1); w2=W(-1,-1); z=W(0)
def mat(entries):
    M=[[z]*5 for _ in range(5)]
    M=[list(r) for r in M]
    for (i,j),v in entries.items(): M[i][j]=v if isinstance(v,W) else W(v)
    return M
u={0:one,1:w,3:w2}; ub={0:one,1:w2,3:w}
B=[]
B.append(mat({**{(i,0):u[i] for i in u},**{(i,3):W(-1)*u[i] for i in u}}))
B.append(mat({(i,1):ub[i] for i in ub}))
B.append(mat({(i,4):ub[i] for i in ub}))
B.append(mat({(0,2):1,(1,2):1,(2,2):-3,(3,2):1}))
for wv in ([1,-2,0,1,0],[0,1,-1,0,0],[0,1,0,0,-1]):
    assert sum(wv)==0 and wv[0]==wv[3]
    B.append(mat({(4,j):wv[j] for j in range(5)}))
# the generic polynomial arithmetic of exact7 uses 0/1 ints and '!=' tests: wrap zero tests
const,rest=level_identity(B)
print('second-kind space: perm(J+t) constant term',const,'; nonzero non-constant coefficients:',len(rest))
