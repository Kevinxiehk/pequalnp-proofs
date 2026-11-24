# Exact Type NC family (product type): M(w0,w1,w3) = { x e_0^T : x in C^4, sum x = 0 } (+) span{ e_0 w0^T, e_1 w1^T, e_3 w3^T },
# w_i supported on columns 1..4, sum w_i = 0, w_i.w_j = 0 (i != j), sum_c w0_c w1_c w3_c = 0.   Column 0 is neutral.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from fractions import Fraction
from t import *
from a1 import embed, defect
from a6 import T1, E0
from r5_FO2 import FO2
def fam(w0,w1,w3):
    B=[]
    for i in (0,1,3):                      # full free column 0 of the 4 rows: e_i - e_2
        m=np.zeros((4,5),complex); m[i,0]=1; m[2,0]=-1; B.append(m)
    for i,w in ((0,w0),(1,w1),(3,w3)):
        m=np.zeros((4,5),complex); m[i,1:]=w; B.append(m)
    return np.array(B)
def exact_level(B,trials=40):
    # exact rational check of the level polynomial at random integer points
    import random
    random.seed(1); Bq=[[[Fraction(int(round(v.real))) for v in row] for row in m] for m in B]
    for _ in range(trials):
        c=[Fraction(random.randint(-5,5)) for _ in B]
        Y=[[1+sum(c[k]*Bq[k][i][j] for k in range(len(B))) for j in range(5)] for i in range(4)]
        s=0
        for f in itertools.permutations(range(5),4):
            p=Fraction(1)
            for i in range(4): p*=Y[i][f[i]]
            s+=p
        if s!=120: return False
    return True
if __name__=='__main__':
    rg=np.random.default_rng(0)
    B=fam([1,-1,0,0],[0,0,1,-1],[1,1,-1,-1])
    print('exact level (40 random integer points):',exact_level(B))
    T=T1(embed(B),rg); E=E0(B,rg); n,rho,bd=FO2(embed(B),rg)
    U,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    print('dim',rank(B.reshape(6,-1)),'e =',int((defect(B)>1e-8).sum()),'dim T1 =',len(T),'dim E0 =',len(E),'dim Omega =',r,'FO2 =',(n,rho,bd))
    print('Omega basis (rows):'); print(np.round(U[:,:r].T.real,3))
    # a complex member: w0=(1,i,-1,-i) isotropic etc.
    w0=np.array([1,1j,-1,-1j]); w1=np.array([1,-1j,-1,1j]); w3=np.array([1,-1,1,-1])
    print('second member: sums',w0.sum(),w1.sum(),w3.sum(),'dots',w0@w1,w0@w3,w1@w3,'triple',(w0*w1*w3).sum())
