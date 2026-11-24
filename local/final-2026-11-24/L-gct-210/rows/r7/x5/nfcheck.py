import numpy as np, itertools
rng=np.random.default_rng(7)
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
def perm(M):
    return sum(np.prod([M[i,p[i]] for i in range(4)]) for p in itertools.permutations(range(4)))
def C(Y):
    J=np.ones((4,5)); return np.array([perm((J+Y)[:,[c for c in range(5) if c!=j]])-24 for j in range(5)])
for trial in range(3):
    a1,a2,b1,b2,mb,md=rng.normal(size=6)+1j*rng.normal(size=6)
    nW=np.array([a1**2-a2**2,1j*(a1**2+a2**2),2*a1*a2]); pW=np.array([b1**2-b2**2,1j*(b1**2+b2**2),2*b1*b2])
    vW=np.cross(nW,pW); n4=H@nW; p4=H@pW; v4=H@vW
    lam=(1+mb)/(1-mb); mu=1/lam; kc=np.sqrt(4/3*(v4@v4))
    m=np.array([1,mb,0,md,-1-mb-md])
    def Y(s1,s2,s3,ph,et):
        A=kc*ph/4+ph*v4+et*n4; Z=np.outer(A,m); t=(lam-1)*et
        Z[:,0]+=t*n4; Z[:,1]-=t*n4
        K=s1*np.outer(v4,[0,0,1,0,0])+s2*np.outer(n4,[1-lam,1+lam,0,0,0])+s3*np.outer(p4,[1-mu,1+mu,0,0,0])
        return K+Z
    x=rng.normal(size=5)+1j*rng.normal(size=5)
    ss=np.array([0.3,0.6,-0.5,0.9]); VM=np.array([[s**k for k in range(1,5)] for s in ss])
    vals=np.array([C(Y(*(s*x))) for s in ss]); co=np.linalg.solve(VM,vals)
    for k in range(4):
        v=co[k]; r=v-v[0]*m   # component outside C m (m_0 = 1)
        print('trial %d degree %d: |C_k|=%.2e  |C_k - C_k[0] m|=%.2e'%(trial,k+1,np.linalg.norm(v),np.linalg.norm(r)))
    # strongly level K alone, and cubic triple condition values
    print('   t(v,n,n)=%.2e t(v,n2,n2)=%.2e'%(abs(np.sum(v4*n4*n4)),abs(np.sum(v4*p4*p4))))
