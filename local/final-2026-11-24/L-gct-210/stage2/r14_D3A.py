# Target 3: FO2-joint for the D003-PROP Case-A family over P^2_alpha (NOTES-stage2 R14-4), with the FULL set of forms q_m (m in X).
#   X = span{ kappa0 = (0,0,1,-1) e_0^T, kappa_s = (1,-1,0,0) e_0^T  (column 0, rows 1..4),  e_3 (x) (0; alpha),  e_4 (x) (0; W1), e_4 (x) (0; W2) },
#   alpha = (1, a2, a3, -1-a2-a3) (chart alpha_1 = 1; WLOG by S_4 on columns 1..4), W1, W2 a basis of alpha^perp cap 1^perp (valid for a2 != 1, which is
#   WLOG too: some coordinate of alpha differs from alpha_1 unless alpha is proportional to 1, impossible).
# Steps as r13_F2col_v2.py: T_1 by rref over Q(a2,a3), rank-jump polynomial, complement, forms = all coefficient matrices (in z) of Q H(J+m) Q^T,
# Rabinowitsch exclusion of bad loci, msolve on all charts (coefficients reduced mod p; FAILED reported separately).
# usage: r14_D3A.py CH [a2=..,a3=..]   env MSV (KB), CHARTS
import sys, itertools, subprocess, os, re, random, sympy as sp
CH=sys.argv[1]; fix={}
if len(sys.argv)>2:
    for kv in sys.argv[2].split(','):
        k,v=kv.split('='); fix[k]=sp.Rational(v)
a2s,a3s=sp.symbols('a2 a3'); A2=fix.get('a2',a2s); A3=fix.get('a3',a3s); par=[v for v in (a2s,a3s) if str(v) not in fix]
al=[sp.Integer(1),A2,A3,-1-A2-A3]
W1=[A3-A2, 1-A3, A2-1, 0]; W2=[al[3]-A2, 1-al[3], 0, A2-1]
def mat(rows):
    M=sp.zeros(5,5)
    for (i,j),v in rows.items(): M[i,j]=v
    return M
Bs=[mat({(3,0):1,(4,0):-1}), mat({(1,0):1,(2,0):-1}), mat({(3,j+1):al[j] for j in range(4)}), mat({(4,j+1):W1[j] for j in range(4)}), mat({(4,j+1):W2[j] for j in range(4)})]
for W in (W1,W2): assert sp.simplify(sum(W))==0 and sp.simplify(sum(a*b for a,b in zip(al,W)))==0
zv=sp.symbols('z1:6'); m=sum((zv[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
def permsym(M):
    n=M.shape[0]
    if n==0: return sp.Integer(1)
    return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
eqs=sp.Poly(expr,*zv).coeffs()
Am=sp.Matrix([[sp.Poly(q,*t).coeff_monomial(t[k]) for k in range(25)] for q in eqs])
from sympy.polys.matrices import DomainMatrix
_dom=sp.QQ.frac_field(*par) if par else sp.QQ
_R,piv=DomainMatrix.from_Matrix(Am).convert_to(_dom).rref(); R=_R.to_Matrix()[:len(piv),:]
free=[c for c in range(25) if c not in piv]
print('dim T_1 =',len(free),flush=True)
rkjump=sp.Integer(1)
if par:
    random.seed(11); g=0
    for _ in range(3):
        rr=sp.Matrix(len(piv),Am.rows,lambda i,j: random.randint(-3,3)); cc=sp.Matrix(25,len(piv),lambda i,j: random.randint(-3,3))
        _cm=DomainMatrix.from_Matrix(rr*Am*cc).convert_to(sp.QQ[tuple(par)]); _d=_cm.det()
        dd=sp.factor(_d.as_expr() if hasattr(_d,'as_expr') else sp.sympify(str(_d))); g=sp.gcd(g,dd) if g!=0 else dd
    rkjump=sp.factor(g); print('rank-jump test polynomial:',rkjump,flush=True)
fs=sp.symbols('f0:%d'%len(free)); tv=[None]*25
for i,c in enumerate(free): tv[c]=fs[i]
for r,c in enumerate(piv): tv[c]=sp.together(-sum(R[r,cc]*tv[cc] for cc in free))
Xf=sp.Matrix([[Bs[k][c//5,c%5] for c in free] for k in range(5)])
random.seed(3); sub={p:sp.Rational(random.randint(2,9),random.randint(2,9)) for p in par}
chosen=None
for S in itertools.combinations(range(len(free)),len(free)-5):
    rest=[i for i in range(len(free)) if i not in S]
    if Xf.subs(sub).extract(list(range(5)),rest).det()!=0: chosen=list(S); restc=rest; break
detX=sp.factor(Xf.extract(list(range(5)),restc).det()); print('complement valid where det != 0:',detX,flush=True)
co=[fs[i] for i in chosen]; nq=len(co)
# complement basis vectors in C^25: set one complement coordinate to 1, the X-pivot free coords to 0
Qrows=[]
for i in range(nq):
    subs_={fs[j]:(1 if j==chosen[i] else 0) for j in range(len(free))}
    Qrows.append([sp.together(tv[c].subs(subs_)) for c in range(25)])
Qm=sp.Matrix(Qrows)
den=sp.lcm([sp.fraction(sp.together(e))[1] for e in Qm]); Qm=(Qm*den).applyfunc(lambda e: sp.expand(sp.cancel(e)))
print('complement scaled by',sp.factor(den),flush=True)
H=sp.zeros(25,25)
for i in range(5):
    for k in range(i+1,5):
        for j in range(5):
            for l in range(5):
                if j==l: continue
                v=permsym(minor(U,[i,k],[j,l])); H[5*i+j,5*k+l]=v; H[5*k+l,5*i+j]=v
F=(Qm*H*Qm.T).applyfunc(sp.expand)
monos=set()
for e in F:
    if e!=0: monos|=set(sp.Poly(e,*zv).monoms())
mats=[F.applyfunc(lambda e: sp.Poly(e,*zv).coeff_monomial(mo) if e!=0 else 0) for mo in sorted(monos)]
print('number of coefficient forms',len(mats),flush=True)
def msstr(e,vars_,p):
    p=int(p); P=sp.Poly(sp.expand(e),*vars_); terms=[]
    for mon,c in P.terms():
        c=sp.Integer(c) if p==0 else sp.Integer(int(c)%p)
        if c==0: continue
        mono='*'.join('%s^%d'%(v,k) if k>1 else str(v) for v,k in zip(vars_,mon) if k>0)
        terms.append(str(c)+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(nq-4)] for r in range(4)]; flat=[v for row in ys for v in row]
wd='/tmp/st2_D3A_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); bad=0; n=0; failed=0
bad_poly=sp.expand(sp.fraction(sp.together(detX))[0]*sp.fraction(sp.together(rkjump))[0]*sp.fraction(sp.together(den))[0]*(A2-1))
CHL=[tuple(int(c) for c in x.split('-')) for x in os.environ.get('CHARTS','').split()]
for S in (CHL or itertools.combinations(range(nq),4)):
    rest=[c for c in range(nq) if c not in S]; Lm=sp.zeros(4,nq)
    for r in range(4):
        Lm[r,S[r]]=1
        for bi,c in enumerate(rest): Lm[r,c]=ys[r][bi]
    polys=[]
    for G in mats:
        Pm=(Lm*G*Lm.T).applyfunc(sp.expand)
        for i in range(4):
            for j in range(i,4):
                if Pm[i,j]!=0: polys.append(Pm[i,j])
    vv=flat+par
    if par:
        wv=sp.Symbol('wB'); polys.append(sp.expand(wv*bad_poly-1)); vv=vv+[wv]
    fn=wd+'/c.ms'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write(','.join(str(v) for v in vv)+'\n'+CH+'\n'+',\n'.join(msstr(q,vv,CH) for q in polys)+'\n')
    subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
    res=open(out).read() if os.path.exists(out) else ''
    body=''.join(l for l in res.splitlines() if not l.startswith('#')); n+=1
    if body.strip()=='':
        failed+=1; print('FAILED chart',S,flush=True); continue
    if re.sub(r'\s','',body)!='[1]:':
        bad+=1; print('NONUNIT chart',S,flush=True)
        if par:
            if os.path.exists(out+'.e'): os.remove(out+'.e')
            subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -e %d -g 2 -t 1 -f %s -o %s.e > /dev/null 2>&1'%(len(flat),fn,out),shell=True)
            el=''.join(l for l in open(out+'.e').read().splitlines() if not l.startswith('#')) if os.path.exists(out+'.e') else ''
            print('   parameter ideal:',re.sub(r',1\*y.*','',el)[:300] or 'FAILED',flush=True)
    elif n%10==0: print('  charts done',n,flush=True)
print('RESULT D3A fix=%s char %s: %d charts, non-unit %d, FAILED %d'%(fix,CH,n,bad,failed),flush=True)
