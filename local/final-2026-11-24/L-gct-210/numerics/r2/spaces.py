import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/numerics')
from core import *
w=np.exp(2j*np.pi/3)
def ex1():
    B=[]
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,0]=w**i; M[i,1]=-w**i
    B.append(M)
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**(2*i); M[i,3]=-w**(2*i)
    B.append(M)
    for j in range(4):
        M=np.zeros((5,5),complex); M[3,j]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def ex2():
    B=[]
    for col in (0,1):
        M=np.zeros((5,5),complex)
        for i in range(3): M[i,col]=w**i
        B.append(M)
    for j in range(4):
        M=np.zeros((5,5),complex); M[3,j]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def angle(B,C):
    Qb=orth(B).reshape(len(B),-1); Qc=orth(C).reshape(len(C),-1)
    s=np.linalg.svd(Qb.conj()@Qc.T,compute_uv=False); return np.sqrt(max(0,1-min(s)**2))
def L080_images():
    """all images of L080 under row/col permutations and transpose: determined by (cross row a, cross col b,
    orientation): 50 spaces"""
    base=L080()  # cross = row 4, col 4, X=0 type
    out=[]
    for a in range(5):
        for b in range(5):
            pr=[x for x in range(5) if x!=a]+[a]; pc=[x for x in range(5) if x!=b]+[b]
            # map row 4 -> a: new[pr[i],pc[j]] = old[i,j]
            for tr in (False,True):
                imgs=[]
                for t in base:
                    s=t.T if tr else t
                    m=np.zeros((5,5),complex)
                    for i in range(5):
                        for j in range(5): m[pr[i],pc[j]]=s[i,j]
                    imgs.append(m)
                out.append(np.array(imgs))
    return out
def genrank(B,seed=3):
    rng=np.random.default_rng(seed); Q=orth(B)
    x=rng.normal(size=len(Q))+1j*rng.normal(size=len(Q)); t=np.einsum('i,iab->ab',x,Q)
    sv=np.linalg.svd(t,compute_uv=False); return int(np.sum(sv>1e-9*sv[0]))
def inv_full(B):
    inv=invariants(B); dE,E,s=ext_space(B)
    gap=(s[24-dE] if dE<25 else None, s[25-dE] if dE<25 and 25-dE<len(s) else None)
    return inv, dE, gap, genrank(B)
import itertools
_perms=list(itertools.permutations(range(5)))
def equiv_angle(A,B):
    """min over row perm, col perm, transpose of sin(max principal angle) between A and image of B"""
    Qa=orth(A).reshape(len(A),-1); Qb=orth(B)
    if len(Qa)!=len(Qb): return 1.0
    best=2.0
    for tr in (False,True):
        Qt=np.transpose(Qb,(0,2,1)) if tr else Qb
        for p in _perms:
            Qp=Qt[:,list(p),:]
            # all column perms at once
            Qpc=np.stack([Qp[:,:,list(q)] for q in _perms]).reshape(120,len(Qb),-1)
            M=np.einsum('ik,pjk->pij',Qa.conj(),Qpc)
            s=np.linalg.svd(M,compute_uv=False)[:,-1]
            v=np.sqrt(np.clip(1-s.max()**2,0,None))
            best=min(best,v)
    return best
def ex3():
    B=[]
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**(2*i); M[i,3]=-w**(2*i)
    B.append(M)
    M=np.zeros((5,5),complex)
    for i in range(3): M[i,2]=w**i; M[i,3]=w**i
    B.append(M)
    for j in range(4):
        M=np.zeros((5,5),complex); M[3,j]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def equiv_angle_c(A,B):
    return min(equiv_angle(A,B),equiv_angle(A,np.conj(B)))
def fam(c,p=0,q=3,cp=None):
    a=np.array([1,-.5,-.5]); b=np.array([0,1,-1.])
    cp=-3/(4*c) if cp is None else cp
    B=[]
    M=np.zeros((5,5),complex); M[:3,p]=a; M[:3,q]=c*b; B.append(M)
    M=np.zeros((5,5),complex); M[:3,p]=cp*b; M[:3,q]=a; B.append(M)
    for j in range(4):
        M=np.zeros((5,5),complex); M[3,j]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
def lim0(p=0):
    B=[]
    for v in ([1,-1,0],[0,1,-1]):
        M=np.zeros((5,5),complex); M[:3,p]=v; B.append(M)
    for j in range(4):
        M=np.zeros((5,5),complex); M[3,j]=1; M[3,4]=-1; B.append(M)
    M=np.zeros((5,5),complex); M[:3,4]=1; M[4,4]=-3; B.append(M)
    return np.array(B)
