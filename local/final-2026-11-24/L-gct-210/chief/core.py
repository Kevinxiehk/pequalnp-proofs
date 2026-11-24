import numpy as np, itertools, sys
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/methods')
n=5
P5=list(itertools.permutations(range(5)))
def perm(A):
    A=np.asarray(A); m=A.shape[0]
    if m==0: return 1.0
    return sum(np.prod([A[i,p[i]] for i in range(m)]) for p in itertools.permutations(range(m)))
w=np.exp(2j*np.pi/3)
def E(i,j,v=1):
    M=np.zeros((5,5),complex); M[i,j]=v; return M
def ex1():
    B=[]
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,0]=w**i; M[i,1]=-w**i
    B.append(M)
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**(2*i); M[i,3]=-w**(2*i)
    B.append(M)
    for j in range(4): B.append(E(3,j)-E(3,4))
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def ex2():
    B=[]
    for col in (0,1):
        M=np.zeros((5,5),complex)
        for i in range(3): M[i,col]=w**i
        B.append(M)
    for j in range(4): B.append(E(3,j)-E(3,4))
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def ex3():
    B=[]
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**(2*i); M[i,3]=-w**(2*i)
    B.append(M)
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**i; M[i,3]=w**i
    B.append(M)
    for j in range(4): B.append(E(3,j)-E(3,4))
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def fam(s,p=0,q=1):
    A=np.array([2,-1,-1]); b=np.array([0,1,-1]); B=[]
    M=np.zeros((5,5),complex); M[:3,p]=A; M[:3,q]=s*b; B.append(M)
    M=np.zeros((5,5),complex); M[:3,p]=-3*b; M[:3,q]=s*A; B.append(M)
    for j in range(4): B.append(E(3,j)-E(3,4))
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def L080():
    B=[]
    for a in range(3): B.append(E(4,a)-E(4,3))
    for b in range(4): B.append(E(b,4)-E(4,4))
    return np.array(B)
def K4():
    z=np.exp(2j*np.pi/5); u=np.array([1,w**2,w,0,0]); ub=np.conj(u); chi=lambda k: z**(k*np.arange(5))
    return np.array([np.outer(u,chi(1)),np.outer(u,chi(4)),np.outer(ub,chi(2)),np.outer(ub,chi(3))])
def K5(j=0):
    B=list(K4()); B.append(E(3,j)-E(4,j)); return np.array(B)
def L9():
    v=np.array([1,1j,-1,-1j,0]); B=[]
    for i in range(5): B.append(np.outer(np.eye(5)[i],v).astype(complex))
    for i in range(4): B.append(E(i,4)-E(4,4))
    return np.array(B)
SP={'L080':L080,'ex1':ex1,'ex2':ex2,'ex3':ex3,'fam2':lambda: fam(2.0),'fam.6+1.4i':lambda: fam(0.6+1.4j),'K5':K5}
def levelerr(B,rng,k=3):
    J=np.ones((5,5)); e=0
    for _ in range(k):
        c=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); e=max(e,abs(perm(J+np.tensordot(c,B,1))-120))
    return e
def nullspace(A,tol=1e-9):
    A=np.atleast_2d(A)
    if A.shape[0]==0: return np.eye(A.shape[1],dtype=complex)
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol*max(1,s[0]))); return vh[r:].conj().T
if __name__=='__main__':
    rng=np.random.default_rng(1)
    for k,f in SP.items():
        B=f(); print(k,len(B),np.linalg.matrix_rank(B.reshape(len(B),-1)),'%.1e'%levelerr(B,rng))
    B=L9(); print('L9',len(B),'%.1e'%levelerr(B,rng))
