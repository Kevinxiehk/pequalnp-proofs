# FO2-joint on the F2col family, parametric (NOTES-stage2 R13-2). RULING in {R1, R2}:
#   R1: P_lam = span{(e, lam f), (f, -3 lam e)} in columns (0,1), rows 1..3   (lam = 0: cross-type; e = (1,-1,0), f = (1,1,-2), R e = f, R f = -3 e)
#   R2: P_nu  = span{(f - 3 nu e, 0), (0, e + nu f)}                          (K33-type: two single-column elements, <v,w> = 0)
#   Z = {z in 1^perp : sum_{k>=1} a_k z_k = 0}, chart a_4 = 1, placed in row 4.
# Steps: T_1 over Q(params) (rref), coordinates = 8 free variables complementary to X (chosen at a random rational point), forms P_2 and B_z
# (z in a basis of Z) restricted, times the lcm of denominators; then msolve on all 70 charts of Gr(4,8) with the parameters as variables
# (char CH); for non-unit charts the chart variables are eliminated and the parameter ideal printed.
# usage: r13_F2col.py RULING CH [FIXPAR=value,...]
import sys, itertools, subprocess, os, re, random, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())

RUL=sys.argv[1]; CH=sys.argv[2]; fix={}
if len(sys.argv)>3:
    for kv in sys.argv[3].split(','):
        k,v=kv.split('='); fix[k]=sp.sympify(v,locals={'a1':sp.Symbol('a1'),'a2':sp.Symbol('a2')})
import pickle, hashlib
_ck='/home/kevxhk/work/L-gct-210/stage2/r14/cache_F2col_%s.pkl'%hashlib.md5((RUL+'|'+(sys.argv[3] if len(sys.argv)>3 else '')).encode()).hexdigest()[:12]
if os.path.exists(_ck):
    lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(_ck,'rb')); print('loaded cached setup',_ck,flush=True)
else:
    lam,nu,a1,a2,a3=sp.symbols('lam nu a1 a2 a3'); par=[lam if RUL=='R1' else nu,a1,a2,a3]
    par=[p for p in par if str(p) not in fix]
    e=[1,-1,0]; f=[1,1,-2]
    L_,N_=fix.get('lam',lam),fix.get('nu',nu); A1,A2,A3=fix.get('a1',a1),fix.get('a2',a2),fix.get('a3',a3)
    def mat(rows):
        M=sp.zeros(5,5)
        for (i,j),v in rows.items(): M[i,j]=v
        return M
    if RUL=='R1':
        P=[mat({**{(k+1,0):e[k] for k in range(3)},**{(k+1,1):L_*f[k] for k in range(3)}}), mat({**{(k+1,0):f[k] for k in range(3)},**{(k+1,1):-3*L_*e[k] for k in range(3)}})]
    else:
        P=[mat({(k+1,0):f[k]-3*N_*e[k] for k in range(3)}), mat({(k+1,1):e[k]+N_*f[k] for k in range(3)})]
    a=[A1,A2,A3,sp.Integer(1)]; Zb=[]
    for k in range(3):
        zz=[-(1-a[k])]+[1 if c==k else 0 for c in range(4)]; zz[4]=zz[4]-a[k]; Zb.append(zz)
    Bs=P+[mat({(4,j):zz[j] for j in range(5)}) for zz in Zb]
    zv=sp.symbols('z1:6'); m=sum((zv[k]*Bs[k] for k in range(5)),sp.zeros(5,5)); U=sp.ones(5,5)+m
    def permsym(M):
        n=M.shape[0]; return sp.expand(sum(sp.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))))
    def minor(M,rows,cols): return M.extract([r for r in range(5) if r not in rows],[c for c in range(5) if c not in cols])
    C=[permsym(minor(U,[i],[j])) for i in range(5) for j in range(5)]
    t=sp.symbols('t0:25'); expr=sp.expand(sum(t[k]*C[k] for k in range(25)))
    eqs=sp.Poly(expr,*zv).coeffs()
    Am=sp.Matrix([[sp.Poly(q,*t).coeff_monomial(t[k]) for k in range(25)] for q in eqs])
    from sympy.polys.matrices import DomainMatrix
    _dom=sp.QQ.frac_field(*par) if par else sp.QQ
    _dm=DomainMatrix.from_Matrix(Am).convert_to(_dom)
    _R,piv=_dm.rref(); R=_R.to_Matrix()[:len(piv),:]
    print('rref done (DomainMatrix over',_dom,')',flush=True)
    free=[c for c in range(25) if c not in piv]
    # rank-jump locus of the T_1 system (gcd of random integer compressions; a superset of the true locus), excluded via Rabinowitsch and REPORTED
    rkjump=sp.Integer(1)
    if par:
        def rndm(r,c_): return sp.Matrix(r,c_,lambda i,j: random.randint(-3,3))
        random.seed(11); g=0
        for _ in range(3):
            _cm=DomainMatrix.from_Matrix(rndm(len(piv),Am.rows)*Am*rndm(25,len(piv))).convert_to(sp.QQ[tuple(par)] if par else sp.QQ)
            dd=sp.factor(_cm.det().as_expr() if hasattr(_cm.det(),'as_expr') else _cm.to_Matrix().det()); g=sp.gcd(g,dd) if g!=0 else dd
        rkjump=sp.factor(g); print('rank-jump test polynomial (T_1 may jump only on its zero set):',rkjump,flush=True)
    print('dim T_1 =',len(free),'free coords',free,flush=True)
    # general element of T_1 in free coordinates
    fs=sp.symbols('f0:%d'%len(free)); tv=[None]*25
    for i,c in enumerate(free): tv[c]=fs[i]
    for r,c in enumerate(piv): tv[c]=sp.together(-sum(R[r,cc]*tv[cc] for cc in free))
    # X in free coordinates; choose 8 free coords complementary to X at a random rational point
    Xf=sp.Matrix([[Bs[k][c//5,c%5] for c in free] for k in range(5)])
    random.seed(3); sub={p:sp.Rational(random.randint(2,9),random.randint(2,9)) for p in par}
    Xn=Xf.subs(sub)
    chosen=None
    for S in itertools.combinations(range(len(free)),len(free)-5):
        rest=[i for i in range(len(free)) if i not in S]
        if Xn.extract(list(range(5)),rest).det()!=0: chosen=list(S); restc=rest; break
    print('complement coordinates (indices into free):',chosen,'; X-pivot coords',restc,flush=True)
    detX=sp.factor(Xf.extract(list(range(5)),restc).det()); print('complement valid where det != 0:',detX,flush=True)
    sub0={fs[i]:0 for i in restc}
    tt=sp.Matrix(5,5,lambda i,j: sp.together(tv[5*i+j].subs(sub0)))
    co=[fs[i] for i in chosen]
    def P2(M):
        tot=0
        for i,k in itertools.combinations(range(M.rows),2):
            for j in range(M.cols):
                for l in range(M.cols):
                    if j!=l: tot+=M[i,j]*M[k,l]
        return tot
    forms=[P2(tt)]
    tau=tt[0:4,:]
    pj=[P2(tau.extract(list(range(4)),[c for c in range(5) if c!=j])) for j in range(5)]
    for zz in Zb: forms.append(sum(zz[j]*pj[j] for j in range(5)))
    forms=[sp.factor(sp.together(F)) for F in forms]
    dens=[sp.fraction(F)[1] for F in forms]; print('denominators:',[sp.factor(d) for d in dens],flush=True)
    forms=[sp.expand(sp.fraction(F)[0]) for F in forms]
    nq=len(co); Gs=[sp.Matrix(nq,nq,lambda i,j: sp.diff(F,co[i],co[j])/(1 if i!=j else 2)) for F in forms]

    pickle.dump((lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix),open(_ck,'wb')); print('saved setup cache',_ck,flush=True)
if os.environ.get('SETUPONLY')=='1': print('SETUPONLY: exiting after setup',flush=True); sys.exit(0)
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(nq-4)] for r in range(4)]; flat=[v for row in ys for v in row]
wd='/tmp/st2_F2col_%s_%d'%(RUL,os.getpid()); os.makedirs(wd,exist_ok=True); bad=0; n=0
CHL=[tuple(int(c) for c in x.split('-')) for x in os.environ.get('CHARTS','').split()]
failed=0
for S in (CHL or itertools.combinations(range(nq),4)):
    rest=[c for c in range(nq) if c not in S]; Lm=sp.zeros(4,nq)
    for r in range(4):
        Lm[r,S[r]]=1
        for bi,c in enumerate(rest): Lm[r,c]=ys[r][bi]
    polys=[]
    for G in Gs:
        Pm=(Lm*G*Lm.T).applyfunc(sp.expand)
        for i in range(4):
            for j in range(i,4):
                if Pm[i,j]!=0: polys.append(Pm[i,j])
    vv=flat+par
    if par and os.environ.get('SAT','1')=='1':   # Rabinowitsch: exclude the bad loci (denominators of the forms, complement determinant)
        wv=sp.Symbol('wB')
        _raw=sp.prod([sp.fraction(sp.together(d))[0] for d in dens])*sp.fraction(sp.together(detX))[0]*sp.fraction(sp.together(rkjump))[0]
        _fl=sp.factor_list(sp.expand(_raw),*par)[1]                     # squarefree part: product of the DISTINCT non-constant irreducible factors
        bad_poly=sp.expand(sp.prod([f for f,e in _fl if sp.Poly(f,*par).total_degree()>0]) if _fl else 1)
        if n==0: print('Rabinowitsch polynomial (squarefree):',sp.factor(bad_poly),flush=True)
        polys.append(sp.expand(wv*bad_poly-1)); vv=vv+[wv]
    fn=wd+'/c.ms'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    open(fn,'w').write(','.join(str(v) for v in vv)+'\n'+CH+'\n'+',\n'.join(msstr(q,vv,CH) for q in polys)+'\n')
    subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
    if os.path.exists(out): os.remove(out) if False else None
    fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)
    res=open(out).read() if fresh else 'NOOUT'
    body=''.join(l for l in res.splitlines() if not l.startswith('#')); unit=re.sub(r'\s','',body)=='[1]:'
    n+=1
    if body.strip()=='' or res=='NOOUT':
        failed+=1; print('FAILED chart',S,'(msolve produced no output: crash or allocation failure)',flush=True); continue
    if not unit:
        bad+=1; print('NONUNIT chart',S,flush=True)
        if par:
            subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -e %d -g 2'%(4*(nq-4))+'  -t 1 -f %s -o %s.e > /dev/null 2>&1'%(fn,out),shell=True)
            el=''.join(l for l in open(out+'.e').read().splitlines() if not l.startswith('#')) if os.path.exists(out+'.e') else 'NOOUT'
            print('   parameter ideal:',re.sub(r',1\*y.*','',el)[:300],flush=True)
    elif n%10==0: print('  charts done',n,flush=True)
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True); print('RESULT F2col %s fix=%s char %s: %d charts, non-unit %d, FAILED %d'%(RUL,fix,CH,n,bad,failed),flush=True)
