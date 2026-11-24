import numpy as np, itertools
w=np.exp(2j*np.pi/3); w2=w*w
B=[]
def Zm(): return np.zeros((5,5),complex)
Z=Zm(); Z[0,:4]=[0,1,w,w2]; B.append(Z)
Z=Zm(); Z[3,:4]=[0,w2,1,w]; B.append(Z)
Z=Zm(); Z[1,:]=[0,w,1,w2,0]; Z[2,:]=-Z[1,:]; B.append(Z)
Z=Zm(); Z[0,0],Z[1,0],Z[2,0]=-2,1,1; B.append(Z)
Z=Zm(); Z[0,0],Z[3,0]=-1,1; B.append(Z)
Z=Zm(); Z[1,:]=[0,w+2,1-w,0,-1]; Z[2,:]=[0,w2-1,w-1,0,1]; B.append(Z)
B=np.array(B)
def perm(A):
    n=A.shape[0]; return sum(np.prod([A[i,f[i]] for i in range(n)]) for f in itertools.permutations(range(n)))
rg=np.random.default_rng(3)
print('level check:',max(abs(perm(np.ones((5,5))+np.tensordot(rg.normal(size=6)+1j*rg.normal(size=6),B,axes=1))-120) for _ in range(5)))
# T_1 numerically: cofactor rows at many random Y
rows=[]
for _ in range(80):
    Y=np.tensordot(rg.normal(size=6)+1j*rg.normal(size=6),B,axes=1); M=np.ones((5,5))+Y
    rows.append([perm(np.delete(np.delete(M,i,0),j,1)) for i in range(5) for j in range(5)])
u,s,vh=np.linalg.svd(np.array(rows)); r=int((s>1e-9*s[0]).sum()); T=vh[r:].conj().reshape(-1,5,5); n=len(T)
print('dim T_1 (numerical) =',n,' singular-value gap',s[r-1]/s[0],s[r]/s[0] if r<len(s) else 0)
for yv in ((1,2,-1,3,1,-2),(2,-1,1,1,-3,1)):
    A5=np.ones((5,5))+np.tensordot(np.array(yv,float),B,axes=1)
    G=np.zeros((n,n),complex)
    for i,k in itertools.permutations(range(5),2):
        for j,l in itertools.permutations(range(5),2):
            h=perm(np.delete(np.delete(A5,[i,k],0),[j,l],1))
            G+=h*np.outer(T[:,i,j],T[:,k,l])
    sv=np.linalg.svd(G,compute_uv=False); print('Y',yv,'singular values of q_Y on T_1:',np.array2string(sv/sv[0],precision=3))
