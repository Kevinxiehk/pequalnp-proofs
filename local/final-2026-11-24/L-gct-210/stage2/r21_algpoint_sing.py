# Recursive kernel bound at an algebraic parameter value of ANY degree, with Singular doing the linear algebra over Q(s) (minpoly) [NOTES-stage2 R21-2].
# The recursion is driven from python: at each node the restricted forms are sent to Singular for rank and kernel (syz over the field Q(s)).
# usage: r21_algpoint_sing.py CACHE "irreducible poly in the parameter" [m=4] [depth=4]
import sys, pickle, subprocess, os, re, random, sympy as sp
ck=sys.argv[1]; pol=sys.argv[2]; M0=int(sys.argv[3]) if len(sys.argv)>3 else 4; DEP=int(sys.argv[4]) if len(sys.argv)>4 else 4
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
t=par[0]; s=sp.Symbol('s'); P=sp.Poly(sp.sympify(pol,locals={str(t):t}).subs(t,s),s)
red=lambda e: sp.expand(sp.rem(sp.expand(sp.sympify(e)),P.as_expr(),s)) if e!=0 else sp.Integer(0)
Gr=[G.subs(t,s).applyfunc(red) for G in Gs]
names=['q0']+['B%d'%z for z in range(1,len(Gs))]
fn='/tmp/st2_aps_%d.sing'%os.getpid(); out=fn+'.out'
def sing(M):          # returns (rank, kernel basis rows as sympy matrix in s)
    n=M.rows
    body='ring r=(0,s),(x),dp;\nshort=0;\nminpoly=%s;\nmatrix A[%d][%d]=%s;\nmodule K=syz(A);\nint rk=%d-size(K);\nstring S=string(rk)+"|";\nint i;int j;\nfor(i=1;i<=size(K);i++){for(j=1;j<=%d;j++){S=S+string(K[i][j])+",";} S=S+";";}\nwrite(":w %s",S);\nquit;\n'%(
        str(P.as_expr()).replace('**','^'),n,n,','.join(str(x).replace('**','^') for x in M),n,n,out)
    open(fn,'w').write(body)
    if os.path.exists(out): os.remove(out)
    subprocess.run('timeout 600 Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    txt=open(out).read().strip(); rk,rest=txt.split('|',1)
    rows=[r_ for r_ in rest.split(';') if r_.strip()]
    Kb=sp.Matrix([[sp.sympify(v.replace('^','**'),locals={'s':s}) for v in r_.split(',') if v!=''] for r_ in rows]) if rows else sp.zeros(0,n)
    return int(rk),Kb
random.seed(1); CW=[random.randint(1,9) for _ in Gs]
def node(basis,m,path,d):
    n=basis.rows; forms=[(basis*G*basis.T).applyfunc(red) for G in Gr]
    rho,_=sing(sum((c*f for c,f in zip(CW,forms)),sp.zeros(n,n))); maxiso=(n-rho)+rho//2
    tag=' > '.join(path)
    if m>maxiso or m>n: print('  %s: dim %d, need %d, max isotropic %d -> CONTRADICTION'%(tag,n,m,maxiso),flush=True); return True
    if m<=0 or d==DEP: return False
    for nm,f in zip(names,forms):
        r,Kb=sing(f)
        if r==0 or r==n or m-r//2<=0: continue
        W=(Kb*basis).applyfunc(red)
        if node(W,m-r//2,path+['ker %s (rank %d on dim %d)'%(nm,r,n)],d+1): return True
    return False
print('fix',fix,'| at root of',P.as_expr(),flush=True)
res=node(sp.eye(nq),M0,['V'],0)
print('RESULT at the algebraic point:', 'KILLED' if res else 'not decided',flush=True)
