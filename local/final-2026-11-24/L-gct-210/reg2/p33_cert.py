# pattern (3|3): forced (hand, NOTES-reg2 9.9) to M = e_0 (x) {w : w_4 = 0, sum w = 0} (+) {x e_4^T : sum x = 0}; exact certificate.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
Z=lambda: sp.zeros(4,5); B=[]
for k in (1,2,3):
    b=Z(); b[0,0]=1; b[0,k]=-1; B.append(b)
for i in (1,2,3):
    b=Z(); b[0,4]=1; b[i,4]=-1; B.append(b)
A5=sp.ones(5,5)+bigY(B); print('level identity:',sp.expand(perm(A5)-120)==0,flush=True)
A=fo_matrix(B); rk=A.rank(); N=sp.Matrix.hstack(*A.nullspace()).T
best=0
for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
    H=hessian(B,yv); best=max(best,(N*H*N.T).rank())
rho=N[:,20:]; print('dim T_1 =',25-rk,' dim Omega =',rho.rank(),' rank q =',best,' => dim L <=',N.shape[0]-(best+1)//2)
