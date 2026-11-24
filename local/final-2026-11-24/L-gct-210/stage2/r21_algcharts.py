# Full Gr(4,nq) FO2-joint charts at an ALGEBRAIC parameter value: Singular over Q(s), minpoly = the irreducible polynomial of the parameter, s := the
# parameter itself [NOTES-stage2 R21-2]. Fixed data (no free parameters), so [1] in all charts = no L'' at that point (and at all its conjugates).
# usage: r21_algcharts.py CACHE "irreducible poly in the parameter"   env STO, MSV, CHARTS
import sys, os, re, itertools, subprocess, pickle, sympy as sp
ck=sys.argv[1]; pol=sys.argv[2]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
t=par[0]; P=sp.Poly(sp.sympify(pol,locals={str(t):t}),t); s=sp.Symbol('s')
red=lambda e: sp.expand(sp.rem(sp.expand(sp.sympify(e).subs(t,s)),P.as_expr().subs(t,s),s)) if e!=0 else e
G2=[G.applyfunc(red) for G in Gs]
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(nq-4)] for r in range(4)]; vv=[v for row in ys for v in row]
def sstr(e):
    Pp=sp.Poly(sp.expand(e),*vv); terms=[]
    for mon,cf in Pp.terms():
        cf=red(cf)
        if cf==0: continue
        mono='*'.join('%s^%d'%(v,k) if k>1 else str(v) for v,k in zip(vv,mon) if k>0)
        terms.append('(%s)'%str(cf).replace('**','^')+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
wd='/tmp/st2_algch_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); n=0; bad=0; slow=0
CHL=[tuple(int(c) for c in x.split('-')) for x in os.environ.get('CHARTS','').split()]
for S in (CHL or itertools.combinations(range(nq),4)):
    rest=[c for c in range(nq) if c not in S]; Lm=sp.zeros(4,nq)
    for r in range(4):
        Lm[r,S[r]]=1
        for bi,c in enumerate(rest): Lm[r,c]=ys[r][bi]
    polys=[]
    for G in G2:
        Pm=(Lm*G*Lm.T).applyfunc(sp.expand)
        for i in range(4):
            for j in range(i,4):
                e=red(Pm[i,j])
                if e!=0: polys.append(e)
    out=wd+'/c.out'; fn=wd+'/c.sing'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write('ring r=(0,s),(%s),dp;\nminpoly=%s;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nif(G[1]==1){write(":w %s","[1]:");}else{write(":w %s","NONUNIT");}\nquit;\n'%(','.join(map(str,vv)),str(P.as_expr().subs(t,s)).replace('**','^'),',\n'.join(sstr(p) for p in polys),out,out))
    subprocess.run('ulimit -v '+os.environ.get('MSV','1500000')+'; timeout '+os.environ.get('STO','300')+' Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    res=open(out).read().strip() if os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn) else 'TIMEOUT'
    n+=1
    if res!='[1]:':
        if res=='TIMEOUT': slow+=1
        else: bad+=1
        print('  chart',S,res,flush=True)
print('RESULT algcharts %s fix=%s at root of %s: %d charts, non-unit %d, timeouts %d'%(os.path.basename(ck),fix,P.as_expr(),n,bad,slow),flush=True)
