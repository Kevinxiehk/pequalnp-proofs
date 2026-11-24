# KERNEL-MEETING REDUCTION, m-dimensional version [NOTES-stage2 R18-1]: ker B_c = K (dim kap), a 4-dim common isotropic L'' meets K in dim >= m.
# Then L'' contains an m-dim q0-isotropic U in K. With K in rref form (pivots p_1..p_kap), U = rowspace(E * Kr), E an m x kap chart matrix (identity in
# columns C), so U has the identity in the coordinates p_C and L'' = U + L', L' a (4-m)-dim subspace of {y_{p_c} = 0, c in C}. Equations: q0 on U,
# all forms on L', q0(U, L') (the B_z vanish on K). Denominators of Kr are cleared and added to the Rabinowitsch factor (exceptional values).
# usage: r18_KU.py CACHE CH M   env ENGINE=sing (STO), MSV
import sys, os, re, itertools, subprocess, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
ck=sys.argv[1]; CH=sys.argv[2]; m=int(sys.argv[3])
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
F=sp.QQ.frac_field(*par); DM=lambda M: DomainMatrix.from_Matrix(M).convert_to(F)
K=DM(sp.Matrix.vstack(*Gs[1:])).nullspace().to_Matrix()
Kr,piv=DM(K).rref() if False else (None,None)
Kd=DomainMatrix.from_Matrix(K).convert_to(F); Rr,piv=Kd.rref(); Kr=Rr.to_Matrix().applyfunc(sp.cancel); kap=Kr.rows
den=sp.lcm([sp.fraction(sp.together(x))[1] for x in Kr])
print('fix',fix,'params',par,'nq',nq,'dim K',kap,'pivots',piv,'denominator of rref(K):',sp.factor(den),flush=True)
excraw=sp.prod([sp.fraction(sp.together(x))[0] for x in list(dens)+[detX,rkjump]])*sp.fraction(sp.together(den))[0]
exc=sp.expand(sp.prod([f for f,e in sp.factor_list(sp.expand(excraw),*par)[1] if sp.Poly(f,*par).total_degree()>0]))
print('Rabinowitsch (exceptional):',sp.factor(exc),flush=True)
w=sp.Symbol('w'); G0=Gs[0]
wd='/tmp/st2_KU_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); n=0; bad=0; failed=0; slow=0
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
Krp=(Kr*den).applyfunc(lambda x: sp.expand(sp.cancel(x)))         # polynomial rows (scaled by den, nonzero off the exceptional set)
for C in itertools.combinations(range(kap),m):
    rest=[c for c in range(kap) if c not in C]
    ss=[[sp.Symbol('s%d_%d'%(r,c)) for c in range(len(rest))] for r in range(m)]
    E=sp.zeros(m,kap)
    for r in range(m):
        E[r,C[r]]=1
        for bi,c in enumerate(rest): E[r,c]=ss[r][bi]
    U=(E*Krp).applyfunc(sp.expand)            # = den * (true U basis), identity*den at pivots p_C
    free=[j for j in range(nq) if j not in [piv[c] for c in C]]
    q=4-m
    for S in itertools.combinations(range(len(free)),q):
        rest2=[c for c in range(len(free)) if c not in S]
        ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(len(rest2))] for r in range(q)]
        Y=sp.zeros(q,nq)
        for r in range(q):
            Y[r,free[S[r]]]=1
            for bi,c in enumerate(rest2): Y[r,free[c]]=ys[r][bi]
        polys=[]
        Pu=(U*G0*U.T).applyfunc(sp.expand)
        for a in range(m):
            for b in range(a,m):
                if Pu[a,b]!=0: polys.append(Pu[a,b])
        Puy=(U*G0*Y.T).applyfunc(sp.expand)
        polys+=[e for e in Puy if e!=0]
        for G in Gs:
            Pm=(Y*G*Y.T).applyfunc(sp.expand)
            for a in range(q):
                for b in range(a,q):
                    if Pm[a,b]!=0: polys.append(Pm[a,b])
        vv=[v for row in ss for v in row]+[v for row in ys for v in row]+list(par)
        if exc!=1: polys.append(sp.expand(w*exc-1)); vv=vv+[w]
        res=solve_sys(polys,vv); n+=1
        if res!='UNIT':
            if res=='NONUNIT': bad+=1
            elif res=='FAILED': failed+=1
            print('  U-chart %s L-chart %s: %s'%(C,S,res),flush=True)
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True)
print('RESULT KU %s fix=%s m=%d char %s engine %s: %d systems, non-unit %d, FAILED %d, Singular-timeouts %d'%(os.path.basename(ck),fix,m,CH,os.environ.get('ENGINE','msolve'),n,bad,failed,slow),flush=True)
