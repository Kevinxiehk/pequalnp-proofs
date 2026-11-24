# KERNEL-MEETING REDUCTION with a parametrised kernel vector [NOTES-stage2 R18-1]. Setting: B_c (generic) has rank r with ker B_c = K (common kernel,
# dim kap), and a 4-dim common isotropic L'' meets K in dim >= 1 (4 - floor(r/2) >= 1). Then L'' contains k = K_j0 + sum_{j != j0} t_j K_j (chart j0)
# with q0(k,k) = 0, and L'' = C k + L3, L3 a 3-dim subspace of {y_i = 0} for an index i with k_i != 0. Runs, for a sequence of indices i_1, i_2, ...:
#   k_{i_1} = ... = k_{i_{s-1}} = 0, u k_{i_s} = 1, L3 in Gr(3, nq-1) charts on {y_{i_s} = 0}; equations: all forms on L3, q0(k, L3) = 0, q0(k,k) = 0,
#   Rabinowitsch w * (exceptional) = 1.  Valid where ker B_c = K (pointwise; exceptional values listed by r18_lineexc.py).
# [Kt2: env SYSLIST='j0:i:a-b-c;...' restricts to the listed systems (re-runs of Singular timeouts)]
# usage: r18_Kt.py CACHE CH   env ENGINE=sing (Singular QQ, per-chart timeout STO) or msolve; MSV
import sys, os, re, itertools, subprocess, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
ck=sys.argv[1]; CH=sys.argv[2]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
K=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix()
K=sp.Matrix.vstack(*[(K.row(i)*sp.lcm([sp.fraction(sp.together(x))[1] for x in K.row(i)])).applyfunc(sp.cancel) for i in range(K.rows)])
kap=K.rows; G0=Gs[0]
print('fix',fix,'params',par,'nq',nq,'dim K',kap,flush=True)
exc=sp.expand(sp.prod([f for f,e in sp.factor_list(sp.expand(sp.prod([sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]])),*par)[1] if sp.Poly(f,*par).total_degree()>0]))
print('Rabinowitsch (exceptional):',sp.factor(exc),flush=True)
ts=sp.symbols('t1:%d'%kap); u,w=sp.symbols('u w')
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(nq-1-3)] for r in range(3)]; flat=[v for row in ys for v in row]
SYSL=set()
for x in os.environ.get('SYSLIST','').split(';'):
    if x.strip():
        a,b,c=x.split(':'); SYSL.add((int(a),int(b),tuple(int(t) for t in c.split('-'))))
wd='/tmp/st2_Kt_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); n=0; bad=0; failed=0; slow=0
def solve_sys(polys,vv):
    global slow
    out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    if os.environ.get('ENGINE')=='sing':
        fn=wd+'/c.sing'
        open(fn,'w').write('ring r=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nif(G[1]==1){write(":w %s","[1]:");}else{write(":w %s","NONUNIT");}\nquit;\n'%(','.join(map(str,vv)),',\n'.join(msstr(q,vv,0) for q in polys),out,out))
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; timeout '+os.environ.get('STO','120')+' Singular -q %s > /dev/null 2>&1'%fn,shell=True)
        if not (os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)): slow+=1; return 'TIMEOUT'
    else:
        fn=wd+'/c.ms'
        open(fn,'w').write(','.join(map(str,vv))+'\n'+CH+'\n'+',\n'.join(msstr(q,vv,CH) for q in polys)+'\n')
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
        if not (os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)): return 'FAILED'
    res=open(out).read(); body=re.sub(r'\s','',''.join(l for l in res.splitlines() if not l.startswith('#')))
    return 'UNIT' if body=='[1]:' else ('FAILED' if body=='' else 'NONUNIT')
for j0 in range(kap):
    tv=list(ts); k=K.row(j0)+sum((tv[jj-(1 if jj>j0 else 0)]*K.row(jj) for jj in range(kap) if jj!=j0),sp.zeros(1,nq))
    tvars=[x for x in ts[:kap-1]]
    qkk=sp.expand((k*G0*k.T)[0,0])
    order=[i for i in range(nq) if any(K[jj,i]!=0 for jj in range(kap))]
    for s_,i in enumerate(order):
        pre=[sp.expand(k[order[q]]) for q in range(s_)]
        # is {k_{i_1}=...=k_{i_s}=0} (with this chart) still possible? (linear in t: check consistency over Q(params))
        idx=[jj for jj in range(nq) if jj!=i]
        for S in itertools.combinations(range(nq-1),3):
            if SYSL and (j0,i,S) not in SYSL: continue
            rest=[c for c in range(nq-1) if c not in S]; Y=sp.zeros(3,nq)
            for r in range(3):
                Y[r,idx[S[r]]]=1
                for bi,c in enumerate(rest): Y[r,idx[c]]=ys[r][bi]
            polys=[p for p in pre if p!=0]+[sp.expand(u*k[i]-1)]
            if qkk!=0: polys.append(qkk)
            for a in range(3):
                e=sp.expand((k*G0*Y.row(a).T)[0,0])
                if e!=0: polys.append(e)
            for G in Gs:
                Pm=(Y*G*Y.T).applyfunc(sp.expand)
                for a in range(3):
                    for b in range(a,3):
                        if Pm[a,b]!=0: polys.append(Pm[a,b])
            vv=flat+tvars+list(par)+[u]
            if exc!=1: polys.append(sp.expand(w*exc-1)); vv=vv+[w]
            res=solve_sys(polys,vv); n+=1
            if res=='UNIT' and os.environ.get('LOGUNIT')=='1': print('UNIT %d:%d:%s'%(j0,i,'-'.join(map(str,S))),flush=True)
            if res!='UNIT':
                if res=='NONUNIT': bad+=1
                elif res=='FAILED': failed+=1
                print('  j0=%d i=%d chart %s: %s'%(j0,i,S,res),flush=True)
        # stop when the vanishing conditions force k = 0 in this chart
        Mx=sp.Matrix([[sp.Poly(sp.expand(k[order[q]]),*tvars).coeff_monomial(x) for x in tvars]+[sp.Poly(sp.expand(k[order[q]]),*tvars).coeff_monomial(1)] for q in range(s_+1)]) if tvars else sp.Matrix([[k[order[q]]] for q in range(s_+1)])
        sz=len(tvars)+1
        if Mx.rows>=sz and any(sp.sympify(sp.expand(Mx.extract(list(rr),list(range(sz))).det())).is_number and sp.expand(Mx.extract(list(rr),list(range(sz))).det())!=0 for rr in itertools.combinations(range(Mx.rows),sz)):
            print('  chart j0=%d: conditions k_i = 0 for i in %s force k = 0 (constant minor) -> done'%(j0,order[:s_+1]),flush=True); break
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True)
print('RESULT Kt %s fix=%s char %s engine %s: %d systems, non-unit %d, FAILED %d, Singular-timeouts %d'%(os.path.basename(ck),fix,CH,os.environ.get('ENGINE','msolve'),n,bad,failed,slow),flush=True)
