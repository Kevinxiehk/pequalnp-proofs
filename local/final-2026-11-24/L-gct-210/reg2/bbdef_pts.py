# exact certificates for the (2,2|1,1)BB row deformations at the leftover points (NOTES-reg2 15.3)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
def cert(j,p,t):
    x=[1,0,p,-1-p]; xp=[x[2]-x[3],0,x[3]-x[0],x[0]-x[2]]; B=[]
    for w in ([1,-1,0,0,0],[0,1,-1,0,0]):
        Jw=[w[1]-w[2],w[2]-w[0],w[0]-w[1],0,0]; m=sp.zeros(4,5); m[0,:]=sp.Matrix([w]); m[j,:]=m[j,:]+t*sp.Matrix([Jw]); B.append(m)
    for w in ([-1,-1,-1,4,-1],[-1,-1,-1,-1,4]):
        m=sp.zeros(4,5); m[1,:]=sp.Matrix([w]); B.append(m)
    m=sp.zeros(4,5); m[:,3]=sp.Matrix(x); B.append(m)
    m=sp.zeros(4,5); m[:,4]=sp.Matrix(xp); B.append(m)
    lev=sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0
    A=fo_matrix(B); N=A.nullspace(); Nm=sp.Matrix.hstack(*N).T; best=0
    for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
        H=hessian(B,yv); best=max(best,(Nm*H*Nm.T).rank())
    print('BB row0->row%d p=%s t=%s: level %s dim T_1 = %d rank q = %d => bound %d'%(j,p,t,lev,len(N),best,len(N)-(best+1)//2),flush=True)
cert(1,sp.Rational(-1,2),1); cert(2,1,1)
