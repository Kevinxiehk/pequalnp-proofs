# K2 reduced charts at an ALGEBRAIC parameter value [NOTES-stage2 R21-2]: s := the parameter, minpoly = its irreducible polynomial (Singular over Q(s)).
# Requires (at the point) B-stack rank nq-1 with constant kernel vector k and rank B_c = nq-1 (then k in L''); q0(k,k) = 0 at the point.
# usage: r21_algK2.py CACHE "irreducible poly"   env STO, MSV
import sys, os, re, itertools, subprocess, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]; pol=sys.argv[2]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
t=par[0]; P=sp.Poly(sp.sympify(pol,locals={str(t):t}),t); s=sp.Symbol('s'); D=None
red=lambda e: sp.expand(sp.rem(sp.expand(sp.sympify(e).subs(t,s)),P.as_expr().subs(t,s),s)) if e!=0 else e
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
k=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
i=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number][0]; k=k/k[i]
assert all(sp.sympify(x).is_number for x in k)
Gs=[G.applyfunc(red) for G in Gs]; G0=Gs[0]
assert red((k*G0*k.T)[0,0])==0, 'q0(k,k) != 0 at the point (then the point is killed by the kernel lemma directly)'
w=(G0*k.T).applyfunc(red); idx=[j for j in range(nq) if j!=i]
j0=[j for j in idx if w[j]!=0][0]; idx2=[j for j in idx if j!=j0]; n7=len(idx2); exc=1
print('fix',fix,'| at root of',P.as_expr(),'| k =',list(k),'| i =',i,'| eliminate j0 =',j0,'(w_j0 =',w[j0],')',flush=True)
ys=[[sp.Symbol('y%d_%d'%(r,cc)) for cc in range(n7-3)] for r in range(3)]; flat=[v for row in ys for v in row]
vv=flat
wd='/tmp/st2_Kt3_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); n=0; bad=0; slow=0
def sstr(e):
    P=sp.Poly(sp.expand(e),*vv); terms=[]
    for mon,cf in P.terms():
        cf=red(cf)
        if cf==0: continue
        mono='*'.join('%s^%d'%(v,kk) if kk>1 else str(v) for v,kk in zip(vv,mon) if kk>0)
        terms.append('(%s)'%str(cf).replace('**','^')+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
for S in itertools.combinations(range(n7),3):
    rest=[cc for cc in range(n7) if cc not in S]; Y=sp.zeros(3,nq)
    for r in range(3):
        Y[r,idx2[S[r]]]=1
        for bi,cc in enumerate(rest): Y[r,idx2[cc]]=ys[r][bi]
        Y[r,j0]=-sum(w[j]*Y[r,j] for j in idx2)
        for j in idx2: Y[r,j]=Y[r,j]*w[j0]
    polys=[]
    for G in Gs:
        Pm=(Y*G*Y.T).applyfunc(red)
        for p_ in range(3):
            for q_ in range(p_,3):
                if Pm[p_,q_]!=0: polys.append(Pm[p_,q_])
    for r in range(3): assert red((k*G0*Y.row(r).T)[0,0])==0
    out=wd+'/c.out'; fn=wd+'/c.sing'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write('ring r=(0,s),(%s),dp;\nminpoly=%s;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nif(G[1]==1){write(":w %s","[1]:");}else{write(":w %s","NONUNIT");}\nquit;\n'%(','.join(map(str,vv)),str(P.as_expr().subs(t,s)).replace('**','^'),',\n'.join(sstr(p) for p in polys),out,out))
    subprocess.run('ulimit -v '+os.environ.get('MSV','1000000')+'; timeout '+os.environ.get('STO','120')+' Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    res=open(out).read().strip() if os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn) else 'TIMEOUT'
    n+=1
    if res!='[1]:':
        if res=='TIMEOUT': slow+=1
        else: bad+=1
        print('  chart',S,res,flush=True)
print('RESULT algK2 %s fix=%s at root of %s: %d charts, non-unit %d, Singular-timeouts %d'%(os.path.basename(ck),fix,P.as_expr(),n,bad,slow),flush=True)
