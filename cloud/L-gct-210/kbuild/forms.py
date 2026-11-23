import sys; sys.path.insert(0,'.')
from core import *
rng=np.random.default_rng(1)
# check E(K) = K + D + C rho
D=[np.outer(np.array([0,0,0,1,-1.]),np.eye(5)[j]) for j in range(5)]
rho=np.outer(np.array([2,2,2,-3,-3.]),np.ones(5))
N=E_of(Kb)
B=np.array([b.ravel() for b in Kb+D+[rho]]).T
print('dim E',N.shape[1],'rank [E|K+D+rho]',np.linalg.matrix_rank(np.hstack([N,B]),1e-8))
# quadratic forms Q_k(X)_{jl} = P_{k-2}(X^{(jl)})
def Q(X,k):
    M=np.zeros((5,5),complex)
    for j in range(5):
        for l in range(5):
            if j!=l: M[j,l]=Pk(np.delete(X,[j,l],1),k-2)
    return M
forms=[]
for s in range(30):
    a=rng.normal(size=4)+1j*rng.normal(size=4)
    X=sum(ai*b for ai,b in zip(a,Kb))[:3]
    for k in (2,3,4,5): forms.append(Q(X,k))
F=np.array([f[np.triu_indices(5)] for f in forms])
print('span of forms dim',np.linalg.matrix_rank(F,1e-8))
for k in (4,5):
    F=np.array([f[np.triu_indices(5)] for f in forms[k-2::4]]); print('k',k,'span',np.linalg.matrix_rank(F,1e-8))
# Fourier coordinates: v = sum nu_c chi_c ; form in nu: Chi^T Q Chi
Chi=np.array([chi(c) for c in range(5)]).T
for k in (4,5):
    print('k',k)
    a=rng.normal(size=4)+1j*rng.normal(size=4)
    X=sum(ai*b for ai,b in zip(a,Kb))[:3]
    G=Chi.T@Q(X,k)@Chi; G[abs(G)<1e-9]=0
    print(np.round(G,3))
