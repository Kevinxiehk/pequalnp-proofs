# Cross family X(a,b) (candidates for L_r): row r = row 0 is zero, i_0 = row 1, j_0 = column 0.
#   X(a,b) = { column 0 = y (y_0 = 0, sum y = 0), row 1 = y_1 e_0 + w (w on columns 1..4, sum w = 0), b y_1 + <a,w> = 0 }   (dim 5)
# Hand result (R6-2): T_1(X) = { column 0 arbitrary, row 1 arbitrary on columns 1..4, row 0 on columns 1..4 = -2 nu a + c0 1,
#   rows 2,3,4 on columns 1..4 = nu a + c 1 } with  sum_j t_1j = nu (sigma_a + b) + 4c  and  sum of all entries = 0   (dim 10).
# Check the hand formula against the numerical T_1, and compute rank of P_2 and of generic q_m on T_1, for random and special (a,b).
import sys, itertools, numpy as np
A=list(sys.argv); sys.argv=[A[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r5_FO2.py').read().split("if __name__=='__main__':")[0])
rg=np.random.default_rng(4)
def E(i,j,v=1.0):
    M=np.zeros((5,5),complex); M[i,j]=v; return M
def Xab(a,b):
    # parametrise: y_1 free, y_2,y_3 free (y_4 = -y_1-y_2-y_3), w in 1^perp (3 free) with b y_1 + <a,w> = 0 -> nullspace of the constraint
    gens=[]; 
    vecs=[]           # coordinates (y1,y2,y3,y4,w1..w4)
    Cst=np.array([[1,1,1,1,0,0,0,0],[0,0,0,0,1,1,1,1],[b,0,0,0]+list(a)],dtype=complex)
    u,s,vh=np.linalg.svd(Cst); ns=vh[3:].conj()
    for v in ns:
        M=np.zeros((5,5),complex); M[1:,0]=v[:4]; M[1,1:]=v[4:]; gens.append(M)
    return gens
def T1_hand(a,b):
    a=np.asarray(a,dtype=complex); sa=a.sum(); cols=[]
    # coordinates: y0..y4, v1..v4, nu, c, c0  (12) with two constraints
    def mat(p):
        y=p[:5]; v=p[5:9]; nu,c,c0=p[9:]; M=np.zeros((5,5),complex); M[:,0]=y; M[1,1:]=v; M[0,1:]=-2*nu*a+c0
        for i in (2,3,4): M[i,1:]=nu*a+c
        return M
    Cst=np.zeros((2,12),complex); Cst[0,5:9]=1; Cst[0,9]=-(sa+b); Cst[0,10]=-4
    Cst[1,:5]=1; Cst[1,5:9]=1; Cst[1,9]=sa; Cst[1,10]=12; Cst[1,11]=4
    u,s,vh=np.linalg.svd(Cst); return np.array([mat(p).ravel() for p in vh[2:].conj()])
def rank(M,tol=1e-8):
    s=np.linalg.svd(M,compute_uv=False); return int((s>tol*max(s[0],1e-300)).sum())
def test(a,b,label=''):
    X=Xab(a,b); n,rho,bd=FO2(X,rg); Th=T1_hand(a,b)
    # numerical T_1
    Mb=np.array(X).reshape(len(X),25); rows=[cof55(np.ones((5,5))+((rg.normal(size=len(X))+1j*rg.normal(size=len(X)))@Mb).reshape(5,5)) for _ in range(60)]
    Aa=np.array(rows); ok=np.abs(Aa@Th.T).max()<1e-8 and rank(Th)==n
    H0=hess(np.ones((5,5),complex)); r0=rank(Th@H0@Th.T)
    print('%-28s dim X = %d, dim T_1 = %d (hand formula agrees: %s), rank P_2 on T_1 = %d, rank generic q_m = %d, FO2 bound = %d'%(label,rank(Mb),n,ok,r0,rho,bd),flush=True)
for k in range(6):
    a=rg.normal(size=4)+1j*rg.normal(size=4); b=rg.normal()+1j*rg.normal(); test(a,b,'random complex #%d'%k)
for a,b,lab in (((1,2,3,5),1,'a=(1,2,3,5), b=1'),((1,2,3,5),0,'b = 0'),((1,-1,0,0),1,'a = e1-e2, b=1'),((1,0,0,0),1,'a = e1, b = 1'),((1,0,0,0),0,'a = e1, b = 0'),
                ((1,1,-1,-1),1,'a=(1,1,-1,-1), b=1'),((1,2,3,-6),1,'sigma_a = 0'),((1,2,3,5),-11,'sigma_a + b = 0'),((1,2,3,-6),0,'sigma_a = b = 0')):
    test(np.array(a,dtype=complex),b,lab)
