import sys; sys.path.insert(0,'.'); sys.path.insert(0,'/home/claude/work/L-gct-086/smallcases')
from core import *
from tangent import weight_space
w=np.exp(2j*np.pi/3)
def E(i,j):
    M=np.zeros((5,5),complex); M[i,j]=1; return M
def L080():
    B=[]
    for j in range(3): B.append(E(0,j+1)-E(0,4))
    for i in range(4): B.append(E(i+1,0)-E(0,0))
    return np.array(B)
def rc45():
    B=[]
    for q,(c0,c1) in enumerate([(0,1),(2,3)]):
        M=np.zeros((5,5),complex)
        for i in range(3):
            z=w**(i*(q+1)); M[i,c0]=z; M[i,c1]=-z
        B.append(M)
    for j in range(4): B.append(E(3,j)-E(3,4))
    return np.array(B)
def rc44():
    B=[]
    for q,(c0,c1) in enumerate([(0,1),(2,3)]):
        M=np.zeros((5,5),complex)
        for i in range(3):
            z=w**(i*(q+1)); M[i,c0]=z; M[i,c1]=-z
        B.append(M)
    for j in range(3): B.append(E(3,j)-E(3,3))
    return np.array(B)
W3=weight_space(5,[1,2,3,4,0],[1,2,0,4,3],30,[2,3,4])
bank={'L080':L080(),'rc45':rc45(),'rc44':rc44(),'W3':W3,'rc45T':np.transpose(rc45(),(0,2,1))}
if __name__=='__main__':
    rng=np.random.default_rng(0)
    for k,B in bank.items():
        c=rnd((30,len(B)),rng); T=np.einsum('rk,kij->rij',c,B)
        res=np.abs(Pk(T)[:,1:]).max()
        I=rde(B); print(k,'dim',len(B),'res %.1e'%res,'r,d,e=',I['r'],I['d'],I['e'])
