import sys; sys.path.insert(0,"/home/claude/work/L-gct-210/stage3")
import numpy as np, itertools
from test_algebra import mul, lin, SUB, IDX, rank
rng=np.random.default_rng(8)
def K_dim(P):
    """dim {Q in A_2 : Q v = 0 in A_3 for all v in P}"""
    rows=[np.array([mul(np.eye(10)[i]+0j,2,lin(v),1) for i in range(10)]).T for v in P]
    return 10-rank(np.concatenate(rows))
def plane(supp):
    P=np.zeros((2,5)); P[:,supp]=rng.normal(size=(2,len(supp))); return P
for supp in ([0,1],[0,1,2],[0,1,2,3],[0,1,2,3,4]):
    print('support size %d: dim K(P) over 5 random planes:'%len(supp),[K_dim(plane(supp)) for _ in range(5)])
# support 4 with K(P) = 1: P spanned by v and v' = D v with r = (1,1,-1,-1)?  (kernels meet in a line)
v=np.zeros(5); v[:4]=rng.normal(size=4); vp=v*np.array([1,1,-1,-1,0]); print('special support-4 plane {v, (1,1,-1,-1) o v}: dim K =',K_dim(np.array([v,vp])))
def triple_dim(Pa,Pb,Pc):
    vecs=[mul(mul(lin(a),1,lin(b),1),2,lin(c),1) for a in Pa for b in Pb for c in Pc]; return rank(np.array(vecs))
print('dim P_aP_bP_c: random planes',triple_dim(plane(range(5)),plane(range(5)),plane(range(5))),
      '; three planes in a coordinate 3-space',triple_dim(plane([0,1,2]),plane([0,1,2]),plane([0,1,2])),
      '; all = span(e_0,e_1)',triple_dim(plane([0,1]),plane([0,1]),plane([0,1])),
      '; two = span(e_0,e_1), third random',triple_dim(plane([0,1]),plane([0,1]),plane(range(5))))
# two-block 3-space V_3 = {<alpha,v> = <beta,v> = 0}: B with B V_3 = 0, symmetric, zero diagonal
def Bspace_dim(V3):
    idx=[(j,l) for j,l in itertools.combinations(range(5),2)]; rows=[]
    for v in V3:
        for m in range(5):
            r=np.zeros(10)
            for n,(j,l) in enumerate(idx):
                if j==m: r[n]=v[l]
                if l==m: r[n]=v[j]
            rows.append(r)
    return 10-rank(np.array(rows))
def perp(vs):
    u,s,vh=np.linalg.svd(np.array(vs)); return vh[len(vs):]
al=np.array([1.,2,0,0,0]); be=np.array([0,0,1.,-1,3]); print('two-block V_3: dim{B} =',Bspace_dim(perp([al,be])),'; random V_3:',Bspace_dim(rng.normal(size=(3,5))),
      '; random 2-plane:',Bspace_dim(rng.normal(size=(2,5))),'; random 4-space:',Bspace_dim(rng.normal(size=(4,5))))
