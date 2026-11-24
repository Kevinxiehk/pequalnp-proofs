# Kt reduction over a QUADRATIC FIELD [NOTES-stage2 R19-1]: dim K = 2 and q0|K = g(params) * M with M a constant 2x2 matrix [[a,b],[b,c]] of non-square
# discriminant D = b^2 - ac. The q0-isotropic lines of K are k = (-b + s) K1 + a K2 with s^2 = D (both conjugates at once: Singular over Q(s) with
# minpoly s^2 - D). Then L'' = C k + L3 with L3 in {y_i = 0} (k_i a nonzero constant of Q(s)), and the linear conditions q0(k, L3) = 0 are eliminated
# (coordinate j0 with w_j0 = (G0 k)_j0 a nonzero constant times excluded factors). Charts Gr(3, nq-2), ~9 chart variables. Singular std over Q(s).
# usage: r18_Kt3.py CACHE   env STO (per-chart Singular timeout), MSV
import sys, os, re, itertools, subprocess, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
ck=sys.argv[1]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
K=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix()
K=sp.Matrix.vstack(*[(K.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in K.row(i)])).applyfunc(sp.cancel) for i in range(K.rows)])
assert K.rows==2, 'needs dim K = 2'
G0=Gs[0]; Q=(K*G0*K.T).applyfunc(sp.factor)
g=sp.gcd(sp.gcd(Q[0,0],Q[0,1]),Q[1,1]); M=(Q/g).applyfunc(sp.cancel)
assert all(sp.sympify(x).is_number for x in M), 'q0|K / gcd is not constant: %s'%M
a,b,c=M[0,0],M[0,1],M[1,1]; D=b*b-a*c
print('fix',fix,'| q0|K = (%s) * %s | discriminant %s (square: %s)'%(sp.factor(g),M.tolist(),D,sp.sqrt(D).is_rational),flush=True)
s=sp.Symbol('s')
if a!=0: k=(-b+s)*K.row(0)+a*K.row(1)
else: k=K.row(0)          # a = 0: K1 itself is isotropic (and the second line needs a separate run; not expected here)
red=lambda e: sp.expand(sp.rem(sp.expand(e),s**2-D,s)) if e!=0 else e
k=k.applyfunc(red); assert red((k*G0*k.T)[0,0])==0
exc=sp.expand(sp.prod([f for f,e in sp.factor_list(sp.expand(sp.prod([sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]])),*par)[1] if sp.Poly(f,*par).total_degree()>0]))
EXCL=[f for f,e in sp.factor_list(exc,*par)[1]] if exc!=1 else []
def admissible(e):            # nonzero constant (in Q(s)) times a product of excluded factors
    e=sp.factor(e)
    if e==0: return False
    num=sp.Poly(e,*par) if e.free_symbols-{s} else None
    if num is None: return True
    fl=[f for f,_ in sp.factor_list(sp.expand(e),*par)[1] if sp.Poly(f,*par).total_degree()>0]
    return all(any(sp.simplify(f/x).is_number for x in EXCL) for f in fl) and not any(s in f.free_symbols for f in fl)
cand=[j for j in range(nq) if admissible(k[j])]
assert cand, 'no index with k_i an admissible constant'
i=cand[0]; w=(G0*k.T).applyfunc(red)
idx=[j for j in range(nq) if j!=i]; cj=[j for j in idx if admissible(w[j])]
assert cj, 'no admissible elimination coordinate'
j0=cj[0]; idx2=[j for j in idx if j!=j0]; n7=len(idx2)
print('k =',[str(x) for x in k],'| complement index i =',i,'| eliminate j0 =',j0,'(w_j0 =',w[j0],')',flush=True)
ys=[[sp.Symbol('y%d_%d'%(r,cc)) for cc in range(n7-3)] for r in range(3)]; flat=[v for row in ys for v in row]
wv=sp.Symbol('wB'); vv=flat+list(par)+([wv] if exc!=1 else [])
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
    if exc!=1: polys.append(sp.expand(wv*exc-1))
    out=wd+'/c.out'; fn=wd+'/c.sing'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write('ring r=(0,s),(%s),dp;\nminpoly=s^2-(%s);\noption(redSB);\nideal I=%s;\nideal G=std(I);\nif(G[1]==1){write(":w %s","[1]:");}else{write(":w %s","NONUNIT");}\nquit;\n'%(','.join(map(str,vv)),D,',\n'.join(sstr(p) for p in polys),out,out))
    subprocess.run('ulimit -v '+os.environ.get('MSV','1000000')+'; timeout '+os.environ.get('STO','120')+' Singular -q %s > /dev/null 2>&1'%fn,shell=True)
    res=open(out).read().strip() if os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn) else 'TIMEOUT'
    n+=1
    if res!='[1]:':
        if res=='TIMEOUT': slow+=1
        else: bad+=1
        print('  chart',S,res,flush=True)
print('RESULT Kt3 %s fix=%s over Q(sqrt(%s)): %d charts, non-unit %d, Singular-timeouts %d'%(os.path.basename(ck),fix,D,n,bad,slow),flush=True)
