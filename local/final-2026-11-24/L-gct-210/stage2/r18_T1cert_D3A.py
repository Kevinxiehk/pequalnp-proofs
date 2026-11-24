# T_1 rank-drop certificate for an F2col (sub)family [NOTES-stage2 R16, target 3].
# rank Am(pi) <= r (generic rank, lower semicontinuity); rank Am(pi) = r  <=  the pivot columns Am[:,piv](pi) have full column rank r.
# So the FULL rank-drop locus (any codimension) is contained in the projection of {(pi,x) : Am[:,piv](pi) x = 0, x in P^(r-1)}.
# Chart systems x_j = 1 (j = 1..r) with a Rabinowitsch variable for the hypersurfaces handled separately (rref denominators, forms' denominators,
# detX, the gcd rank-jump polynomial).  All charts [1]  =>  no rank drop of T_1 outside those hypersurfaces.  Engines: msolve mod p / Singular QQ.
# usage: r18_T1cert_D3A.py CH [a2=..,a3=..]   env EXC, ENGINE=sing, MSV, ELIM  (D003-PROP Case A family of r14_D3A_fx.py)
import sys, os, re, subprocess
_args=sys.argv[:]; sys.argv=['r14_D3A_fx.py',_args[1]]+(_args[2:3] if len(_args)>2 and _args[2] else [])
src=open('/home/kevxhk/work/L-gct-210/stage2/r14_D3A_fx.py').read()
pre=src.split("free=[c for c in range(25) if c not in piv]")[0]
exec(pre); RUL='D3A'; CH=_args[1]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
r=len(piv); print('family',RUL,fix,'ZBASIS',os.environ.get('ZBASIS',''),' params',par,' generic rank',r,' rows',Am.rows,flush=True)
dens_r=sp.Integer(1)
for e in R:
    if e!=0: dens_r=sp.lcm(dens_r,sp.fraction(sp.together(e))[1])
dens_r=sp.factor(dens_r); print('lcm of rref denominators:',dens_r,flush=True)
if not par: print('fixed member: rank at the point =',sp.Matrix(Am).rank(),flush=True); sys.exit(0)
Ap=sp.Matrix(Am).extract(list(range(Am.rows)),list(piv))
# clear denominators row-wise (Am has polynomial entries in the parameters already; keep exact)
EXTRA=os.environ.get('EXC','')        # extra hypersurfaces (comma-separated) to exclude, e.g. the forms' denominators and detX from the setup log
excl=[dens_r]+[sp.sympify(x,locals={str(p):p for p in par}) for x in EXTRA.split(',') if x]
fl=[]
for x in excl:
    for f,e in sp.factor_list(sp.expand(sp.fraction(sp.together(x))[0]),*par)[1]:
        if sp.Poly(f,*par).total_degree()>0 and not any(sp.simplify(f/g).is_number for g in fl): fl.append(f)
bad=sp.expand(sp.prod(fl)) if fl else sp.Integer(1); print('excluded hypersurfaces:',fl,flush=True)
xs=sp.symbols('x0:%d'%r); wv=sp.Symbol('wB')
wd='/tmp/st2_T1cert_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); n=0; nonunit=0; failed=0
rows=[sp.expand(sum(Ap[i,j]*xs[j] for j in range(r))) for i in range(Ap.rows)]
rows=[q for q in rows if q!=0]
for j in range(r):
    polys=[q.subs(xs[j],1) for q in rows]+[q for q in [xs[l] for l in range(j)]]   # chart: x_j = 1, x_l = 0 for l < j (disjoint cover of P^(r-1))
    vv=[x for l,x in enumerate(xs) if l>j]+list(par)
    if bad!=1: polys.append(sp.expand(wv*bad-1)); vv=vv+[wv]
    polys=[sp.expand(q.subs({xs[l]:0 for l in range(j)})) for q in polys]; polys=[q for q in polys if q!=0]
    out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    if os.environ.get('ENGINE')=='sing':
        fn=wd+'/c.sing'
        open(fn,'w').write('ring rr=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nwrite(":w %s", string(G));\nquit;\n'%(','.join(map(str,vv)),',\n'.join(msstr(q,vv,0) for q in polys),out))
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; Singular -q %s > /dev/null 2>&1'%fn,shell=True)
        fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn); res=open(out).read().strip() if fresh else 'NOOUT'
        unit=re.sub(r'\s','',res)=='1'; empty=(res=='NOOUT' or res=='')
    else:
        fn=wd+'/c.ms'
        open(fn,'w').write(','.join(map(str,vv))+'\n'+CH+'\n'+',\n'.join(msstr(q,vv,CH) for q in polys)+'\n')
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
        fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn); res=open(out).read() if fresh else 'NOOUT'
        body=''.join(l for l in res.splitlines() if not l.startswith('#')); unit=re.sub(r'\s','',body)=='[1]:'; empty=(res=='NOOUT' or body.strip()=='')
    n+=1
    if empty: failed+=1; print('FAILED chart x%d=1'%j,flush=True)
    elif not unit:
        nonunit+=1; print('NONUNIT chart x%d=1'%j,flush=True)
        if os.environ.get('ELIM')=='1':   # structure of the parameter locus (char 32003, evidence): eliminate x and w, minimal associated primes
            fe=wd+'/e.sing'; oe=wd+'/e.out'
            if os.path.exists(oe): os.remove(oe)
            xv=[str(x) for x in vv if str(x) not in [str(q) for q in par]]
            open(fe,'w').write('LIB "primdec.lib";\nring rr=32003,(%s,%s),dp;\nideal I=%s;\nideal E=eliminate(I,%s);\nring ss=32003,(%s),dp;\nideal E=imap(rr,E);\nlist L=minAssGTZ(E);\nstring S="";\nfor(int i=1;i<=size(L);i++){S=S+string(L[i])+" | ";}\nwrite(":w %s",S);\nquit;\n'%(','.join(xv),','.join(map(str,par)),',\n'.join(msstr(q,vv,32003) for q in polys),'*'.join(xv),','.join(map(str,par)),oe))
            subprocess.run('ulimit -v 2000000; timeout 900 Singular -q %s > /dev/null 2>&1'%fe,shell=True)
            print('   parameter locus (minimal primes, char 32003):',open(oe).read().strip()[:800] if os.path.exists(oe) else 'ELIM FAILED',flush=True)
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True)
print('RESULT T1cert %s fix=%s char %s: %d charts, non-unit %d, FAILED %d'%(RUL,fix,CH,n,nonunit,failed),flush=True)
