import numpy as np, itertools, sys
sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases'); import level
I=1j; chi=lambda a: np.array([I**(a*j) for j in range(4)])
def E(v,j):
    t=np.zeros((4,5),complex); t[:,j]=v; return t
def test(basis,name):
    B=np.array([b.ravel() for b in basis]); k=np.linalg.matrix_rank(B,1e-9)
    rng=np.random.default_rng(0); S=rng.normal(size=(40,len(B)))+1j*rng.normal(size=(40,len(B)))
    Y=(S@B).reshape(-1,4,5)
    # strongly level: all column deletions 4x4 level
    worst=np.zeros(5)
    for j in range(5):
        Z=np.delete(Y,j,axis=2); P=level.Pk(Z); worst=np.maximum(worst,abs(P).max(0))
    # full 5x5 level with free row 4
    T=np.zeros((40,5,5),complex); T[:,:4,:]=Y; w=rng.normal(size=(40,5))+1j*rng.normal(size=(40,5)); w-=w.mean(1,keepdims=True); T[:,4,:]=w
    P5=abs(level.Pk(T)).max(0)
    print(name,'dim',k,'deletion |P1..P4| max',np.round(worst[1:],12),' 5x5 with free row |P1..P5|',np.round(P5[1:],12))
c1,c2,c3=chi(1),chi(2),chi(3)
test([E(c1,0),E(c1,1),E(c1,2)],'chi1 x C^3')
test([E(c1,0),E(c1,1),E(c1,2),E(c2,0)],'caseA: + chi2 e_0')
for pi in [0.0,1.0,0.7+0.3j]:
    test([E(c1,0),E(c1,1),E(c1,2),E(c2+pi*c1,3)-E(pi*c1,4)],'caseB pi=%s'%pi)
test([E(c1,0),E(c1,1),E(c1,2),E(c1,3)],'chi1 x C^4')
