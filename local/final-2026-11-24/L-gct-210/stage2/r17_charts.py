# Full Gr(4,nq) FO2-joint chart run on ANY cached setup (r16/ caches incl. ZBASIS / R2inf) [NOTES-stage2 R17]. Hardened writer + freshness check.
# usage: r17_charts.py CACHE CH      env CHARTS, MSV, SAT
import sys, itertools, subprocess, os, re, pickle, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
ck=sys.argv[1]; CH=sys.argv[2]; RUL=os.path.basename(ck)
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
print('cache',ck,'fix',fix,'params',par,'nq',nq,flush=True)
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
    if os.environ.get('ENGINE')=='sing':
        fn=wd+'/c.sing'
        open(fn,'w').write('ring r=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nif(G[1]==1){write(":w %s","[1]:");}else{write(":w %s","NONUNIT "+string(G[1]));}\nquit;\n'%(','.join(str(v) for v in vv),',\n'.join(msstr(q,vv,0) for q in polys),out,out))
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; timeout '+os.environ.get('STO','120')+' Singular -q %s > /dev/null 2>&1'%fn,shell=True)
        if not (os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)):   # Singular timed out: fall back to msolve char 0 for this chart
            fn2=wd+'/c.ms'
            open(fn2,'w').write(','.join(str(v) for v in vv)+'\n0\n'+',\n'.join(msstr(q,vv,0) for q in polys)+'\n')
            subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; timeout 900 msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn2,out),shell=True)
            fn=fn2; print('   chart',S,'Singular timed out -> msolve char 0 [M0]',flush=True)
    else:
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
