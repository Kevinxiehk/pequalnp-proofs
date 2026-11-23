import numpy as np
n=5; w=np.exp(2j*np.pi/3); z=np.exp(2j*np.pi/5)
def M(f):
    t=np.zeros((n,n),dtype=complex); f(t); return t.ravel()
def ex1():
    v=np.array([1,w,w**2]); B=[]
    B.append(M(lambda t: (t.__setitem__((slice(0,3),0),v), t.__setitem__((slice(0,3),1),-v))))
    B.append(M(lambda t: (t.__setitem__((slice(0,3),2),v**2), t.__setitem__((slice(0,3),3),-v**2))))
    for j in range(4): B.append(M(lambda t,j=j: (t.__setitem__((3,j),1), t.__setitem__((3,4),-1))))
    B.append(M(lambda t: t.__setitem__((slice(None),4),np.array([1,1,1,0,-3]))))
    return np.array(B)
def ex2():
    v=np.array([1,w,w**2,0,0]); B=[]
    B.append(M(lambda t: t.__setitem__((slice(None),0),v))); B.append(M(lambda t: t.__setitem__((slice(None),1),v)))
    for j in range(4): B.append(M(lambda t,j=j: (t.__setitem__((3,j),1), t.__setitem__((3,4),-1))))
    B.append(M(lambda t: t.__setitem__((slice(None),4),np.array([1,1,1,0,-3]))))
    return np.array(B)
def ex1DC(): return ex1()[:2]
def rank1weight():   # u (x) v, u = 5th roots, v sum zero with v_4 = 0 : DC level, dim 3
    u=z**np.arange(5); B=[]
    for j in range(3):
        v=np.zeros(5); v[j]=1; v[3]=-1; B.append(np.outer(u,v).ravel())
    return np.array(B,dtype=complex)
def circ4():
    f=np.array([1,1j,-1j,-1]); t=np.zeros((n,n),dtype=complex)
    for i in range(4):
        for j in range(4): t[i,j]=f[(j-i)%4]
    return t.ravel()[None,:]
def L080():
    B=[]
    for a in range(3): B.append(M(lambda t,a=a: (t.__setitem__((4,a),1), t.__setitem__((4,3),-1))))
    for b in range(4): B.append(M(lambda t,b=b: (t.__setitem__((b,4),1), t.__setitem__((4,4),-1))))
    return np.array(B)
SP={'ex1':ex1,'ex2':ex2,'ex1DC':ex1DC,'rank1weight':rank1weight,'circ4':circ4,'L080':L080}
if __name__=='__main__':
    import itertools, math
    P=list(itertools.permutations(range(n)))
    def perm(A): return sum(np.prod([A[i,p[i]] for i in range(n)]) for p in P)
    rng=np.random.default_rng(0)
    for k,f in SP.items():
        B=f(); err=max(abs(perm(np.ones((n,n))+np.tensordot(rng.normal(size=len(B))+1j*rng.normal(size=len(B)),B.reshape(-1,n,n),1))-120) for _ in range(3))
        print(k,'dim',np.linalg.matrix_rank(B),'level err %.1e'%err); np.save('sp_'+k+'.npy',B)
