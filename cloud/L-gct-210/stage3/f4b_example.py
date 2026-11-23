# Round 7: the explicit 7-dim level space M_0 of F4b-core shape (free column (+) D).  EXACT check in Z[omega] at random integer points,
# and dim T_1(M_0), a_r, lam, z numerically.   omega = primitive cube root of unity; elements a + b*omega stored as pairs, omega^2 = -1 - omega.
import itertools, random, numpy as np
def mul(x,y): a,b=x; c,d=y; return (a*c-b*d, a*d+b*c-b*d)
def add(x,y): return (x[0]+y[0],x[1]+y[1])
ONE=(1,0); ZERO=(0,0); OM=(0,1); OM2=(-1,-1)
def sc(k,x): return (k*x[0],k*x[1])
n1=[ZERO,ONE,OM2,ZERO,OM]      # columns 1..5 ; n = (1, w^2, 0, w) on columns 2,3,4,5 -> support columns 2,3,5
n2=[ZERO,ONE,OM,ZERO,OM2]
w =[ZERO,sc(-1,ONE),sc(-1,ONE),sc(3,ONE),sc(-1,ONE)]
e1=[ONE,ZERO,ZERO,ZERO,ZERO]; me1=[sc(-1,ONE),ZERO,ZERO,ZERO,ZERO]
Z5=[ZERO]*5
def mat(rows): return [list(r) for r in rows]
B=[]
for r in range(4):
    M=[Z5[:] for _ in range(5)]; M[r]=e1[:]; M[4]=me1[:]; B.append(M)          # x^{re} = e_r e_1^T - e_e e_1^T
M=[Z5[:] for _ in range(5)]; M[4]=w[:]; B.append(M)                             # e_e w^T
M=[Z5[:] for _ in range(5)]; M[0]=n1[:]; M[1]=[sc(-1,t) for t in n1]; B.append(M)   # G_ab = e_a n^T - e_b n^T
M=[Z5[:] for _ in range(5)]; M[2]=n2[:]; M[3]=[sc(-1,t) for t in n2]; B.append(M)   # G_cd = e_c n'^T - e_d n'^T
def perm(A):
    tot=ZERO
    for q in itertools.permutations(range(5)):
        t=ONE
        for i in range(5): t=mul(t,A[i][q[i]])
        tot=add(tot,t)
    return tot
random.seed(7); bad=0; NP=900
for _ in range(NP):
    c=[(random.randint(-9,9),random.randint(-9,9)) for _ in range(7)]
    A=[[add(ONE,ZERO) for _ in range(5)] for _ in range(5)]
    for k in range(7):
        for i in range(5):
            for j in range(5): A[i][j]=add(A[i][j],mul(c[k],B[k][i][j]))
    if perm(A)!=(120,0): bad+=1
print('exact check: perm(J+m) = 120 at %d random points of M_0 with coefficients in Z[omega]: failures %d'%(NP,bad))
om=np.exp(2j*np.pi/3); Bn=np.array([[[x[0]+x[1]*om for x in row] for row in M] for M in B])
def rank(A,tol=1e-8):
    s=np.linalg.svd(np.atleast_2d(A),compute_uv=False); return int((s>tol*max(1,s[0])).sum())
P4=np.array(list(itertools.permutations(range(4))))
def cofs(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=np.delete(np.delete(M,i,axis=0),j,axis=1); out.append(A[np.arange(4)[None,:],P4].prod(axis=1).sum())
    return np.array(out)
rg=np.random.default_rng(1); A=np.array([cofs(np.ones((5,5))+np.tensordot((rg.normal(size=7)+1j*rg.normal(size=7))*0.7,Bn,axes=1)) for _ in range(120)])
s=np.linalg.svd(A,compute_uv=False); rk=int((s>1e-8*s[0]).sum()); print('dim M_0 =',rank(Bn.reshape(7,25)),' dim T_1(M_0) =',25-rk,' (gap %.1e / %.1e)'%(s[rk-1]/s[0], s[rk]/s[0] if rk<25 else 0))
def ker(rows): return 7-rank(np.array([[Bn[k][i,j] for k in range(7)] for i in rows for j in range(5)]))
print('a_r',[5-rank(Bn[:,r,:]) for r in range(5)],' dim M_r',[ker([r]) for r in range(5)],' z',[ker([i for i in range(5) if i!=r]) for r in range(5)],
      ' lam',{(r,q):ker([r,q]) for r in range(5) for q in range(r+1,5)})
