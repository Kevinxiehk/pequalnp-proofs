# exact certificates for (2,1,1|1,1): (a,a) leftover points (dim T_1, rank q over Q / Q(sqrt -3)), x-infinity points, (I-a)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from dr211_special import perm, bigY, fo_matrix, hessian
def rowel(i,w): m=sp.zeros(4,5); m[i,:]=sp.Matrix([w]); return m
def colel(c,x): m=sp.zeros(4,5); m[:,c]=sp.Matrix(x); return m
K=sp.QQ.algebraic_field(sp.sqrt(-3))
def cert(B,name):
    lev=sp.expand(perm(sp.ones(5,5)+bigY(B))-120)==0
    A=fo_matrix(B); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(K); n=25-dm.rank(); N=dm.nullspace().to_Matrix(); best=0
    for yv in [(1,2,-1,3,1,-2),(2,-1,1,1,-3,1)]:
        H=hessian(B,yv); best=max(best,sp.polys.matrices.DomainMatrix.from_Matrix((N*H*N.T).applyfunc(sp.expand)).convert_to(K).rank())
    print('%-40s level %s dim T_1 = %d rank q = %d => bound %d'%(name,lev,n,best,n-(best+1)//2),flush=True)
c3=lambda u:[u[1]-u[2],u[2]-u[0],u[0]-u[1],0,0]
cr=lambda x:[0,x[2]-x[3],x[3]-x[1],x[1]-x[2]]
U0=[rowel(0,[-1,-1,-1,4,-1]),rowel(0,[-1,-1,-1,-1,4])]
h=sp.Rational(1,2); w=sp.Rational(-1,2)+sp.sqrt(-3)/2
for (s,p) in ([] if ('ab' in sys.argv or 'iso' in sys.argv or 'II' in sys.argv) else [(1,-h),(-2,-h),(-h,-h),(0,-2),(-1,-2),(-2,1),(w,1),(0,0),(-1,0)]):
    u1=[1,s,sp.expand(-1-s),0,0]; x=[0,1,p,-1-p]
    cert(U0+[rowel(1,u1),rowel(2,[sp.expand(e) for e in c3(u1)]),colel(3,x),colel(4,cr(x))],'(2,1,1|1,1)aa s=%s p=%s'%(s,p))
if not set(['ab','iso','II'])&set(sys.argv): cert([rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,-1,0,0]),rowel(1,[-1,-1,-1,0,3]),rowel(2,[-1,-1,-1,4,-1]),colel(3,[1,-2,0,1]),colel(4,[1,0,0,-1])],'(2,1,1|1,1)I-a')
if 'ab' in sys.argv:
    g=[1,1,1,0,-3]
    for (s_,q) in [(-1,0),(-h,0),(1,0),(-2,0),(-1,4),(-1,-2),(0,w),(-1,-h),(0,2),(-1,1),(0,-1),(0,h)]:
        u1=[1,s_,-1-s_,0,0]; u2=[sp.expand(g[j]+q*c3(u1)[j]) for j in range(5)]
        W=sp.Matrix([[1]*5,u1,u2]).nullspace()
        cert([rowel(0,[sp.expand(e) for e in v]) for v in W]+[rowel(1,u1),rowel(2,u2),colel(3,[0,1,-2,1]),colel(4,[0,1,0,-1])],'(2,1,1|1,1)ab s=%s q=%s'%(s_,q))
if 'iso' in sys.argv:
    l=[1,w,sp.expand(w**2),0,0]; U0i=[rowel(0,[1,1,1,-3,0]),rowel(0,[0,0,0,1,-1])]
    for p in [0,-2,-h,1,w,sp.expand(w**2),None]:
        x=[0,0,1,-1] if p is None else [0,1,p,sp.expand(-1-p)]
        cert(U0i+[rowel(1,l),rowel(2,l),colel(3,x),colel(4,[sp.expand(e) for e in cr(x)])],'(2,1,1|1,1)IV-iso p=%s'%('inf' if p is None else p))
if 'II' in sys.argv:
    wv=[1,0,-1,0,0]; W=sp.Matrix([[1]*5,[0,0,0,1,0],wv]).nullspace()
    cert([rowel(0,list(v)) for v in W]+[rowel(1,wv),rowel(2,[-1,-1,-1,4,-1]),colel(3,[-2,1,0,1]),colel(4,[0,1,0,-1])],'(2,1,1|1,1)II-2b s=0')
