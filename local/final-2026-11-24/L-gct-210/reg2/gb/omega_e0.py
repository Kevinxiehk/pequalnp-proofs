# Generic Omega / E_0 certificate (round 8): dim T_1 <= 9 for every member of a (possibly skew-deformed) family from gen_rank.py FAMS.
#   usage: omega_e0.py FAMILY DEFO OMEGA DDIR [NPIV]
#     DEFO  = none | kind,idx,tgt         (skew deformation as in gen_rank_defo.py, new parameter t)
#     OMEGA = c                            (expected Omega = span(1, e_c): normalisation rho_c = 0, sum_{j != c} rho_j = 0, charts rho_j = 1, j != c)
#     DDIR  = row,i | col,c               (the extra E_0 direction d: (e_i - 1/4) (x) 1  or  1 (x) (e_c - 1/5); scaled by 4 resp. 5)
#   Omega-test: X FREE (no pivots), family relations + FO equations + rho normalisation + chart; eliminate X, rho -> ideal in the parameters.
#   E_0-test: rho = 0, X normalised modulo M + C d at 7 pivot coordinates chosen numerically (NPIV pivot sets, each localised by z*Delta = 1,
#   Delta = the 7x7 pivot minor); the pivot sets must cover the family: ideal(Delta_1, .., Delta_NPIV, relations) = (1) is checked too.
import sys, subprocess, random, itertools; sys.argv_orig=list(sys.argv); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
import numpy as np
fam,defo,omc,ddir=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4]; npiv=int(sys.argv[5]) if len(sys.argv)>5 else 2
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); cut=src.index('F=Family(params,bfn,d)')
sys.argv=['x',fam,'16','1','1']; exec(src[:cut])
base_bfn=bfn; P=list(params)
if defo!='none':
    kind,idx,tgt=defo.split(','); idx=int(idx); tgt=int(tgt)
    def support(B):
        cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
    def dotv(a,b):
        t={}
        for x,y in zip(a,b):
            if x and y: t=add(t,mul(x,y))
        return t
    DEFO2=None
    for _a in sys.argv_orig[6:]:
        if _a.startswith('defo2='): _k,_i,_t=_a[6:].split(','); DEFO2=(_k,int(_i),int(_t))
    def _apply(Bs,kind,idx,tgt):
        grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
        v=[[Bs[g][i][idx] for i in range(4)] if kind=='col' else [Bs[g][idx][j] for j in range(5)] for g in grp]
        g11=dotv(v[0],v[0]); g12=dotv(v[0],v[1]); g22=dotv(v[1],v[1])
        Jv=[[add(mul(g12,v[0][k]) if v[0][k] else {}, mul(g11,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))],
            [add(mul(g22,v[0][k]) if v[0][k] else {}, mul(g12,v[1][k]) if v[1][k] else {},-1) for k in range(len(v[0]))]]
        return grp,Jv
    def bfn(R,V):        # round 10: optional second deformation (parameter t2); J-maps computed on the undeformed basis (as in lift_gram.py)
        Bs=base_bfn(R,V)
        specs=[(kind,idx,tgt,V('t'))]+([(DEFO2[0],DEFO2[1],DEFO2[2],V('t2'))] if DEFO2 else [])
        pre=[_apply(Bs,k_,i_,g_) for (k_,i_,g_,t_) in specs]
        for (k_,i_,g_,t_),(grp,Jv) in zip(specs,pre):
            for n,g in enumerate(grp):
                for k in range(len(Jv[n])):
                    if Jv[n][k]:
                        if k_=='col': Bs[g][k][g_]=add(Bs[g][k][g_],mul(t_,Jv[n][k])) if Bs[g][k][g_] else mul(t_,Jv[n][k])
                        else: Bs[g][g_][k]=add(Bs[g][g_][k],mul(t_,Jv[n][k])) if Bs[g][g_][k] else mul(t_,Jv[n][k])
        return Bs
    P=P+['t']+(['t2'] if DEFO2 else [])
F=Family(P+['z'],bfn,d); W=F.W; names=F.names; npar=len(P)+1
rels=[{k[:npar]:v for k,v in q.items()} for q in F.level]
FAMREL=list(FAMS[fam][3])
if FAMREL:
    import sympy as _sp
    for _r in FAMREL:
        _syms=_sp.symbols(' '.join(names)); _p=_sp.Poly(_sp.sympify(_r.replace('^','**')),*_syms)
        rels.append({tuple(m):int(c) for m,c in _p.terms()})

# exact spanning set of M + C d in the reduced ring
Rr=Ring(names); Bs=bfn(F.R,F.R.var)
def red(q): return {k[d:]:v for k,v in q.items()} if q else {}
span=[[[red(B[i][j]) for j in range(5)] for i in range(4)] for B in Bs]
kd,vd=ddir.split(','); vd=int(vd)
if kd=='row': D=[[F.c(3 if i==vd else -1) for j in range(5)] for i in range(4)]
else: D=[[F.c(4 if j==vd else -1) for j in range(5)] for i in range(4)]
span.append(D)
def strq(q): return to_str_Q(q,names) if q else '0'
def sing(polys,elim=None,body=None):
    lines=[strq(q) if isinstance(q,dict) else q for q in polys]; lines=[l for l in lines if l!='0']
    if body is None: body=('ideal J=eliminate(I,%s);\nJ=std(J);\nprint(J);'%elim) if elim else 'ideal G=std(I);\nprint(size(G));print(G[1]);'
    open('/tmp/oe0_%s.sing'%fam,'w').write('ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\n%s\nquit;\n'%(','.join(names),',\n'.join(lines),body))
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/oe0_%s.sing'%fam),capture_output=True,text=True,timeout=1700)
    return ' '.join(r.stdout.split())[:3000]
el='*'.join(['z']+F.xv+F.rv)
# ---- Omega-test (X free)
others=[j for j in range(5) if j!=omc]; s=W('r%d'%others[0])
for j in others[1:]: s=add(s,W('r%d'%j))
om_ok=True
for jr in others:
    out=sing(rels+F.fo+[W('r%d'%omc),s,F.eq('r%d'%jr,1)],el); u=(out.strip()=='1'); om_ok=om_ok and u
    print('Omega-test rho_%d=1: %s'%(jr,'UNIT' if u else out[:200]),flush=True)
print('  CAL rho = e_%d (must be non-unit):'%omc,sing(rels+F.fo+[F.eq('r%d'%omc,1)]+[W('r%d'%j) for j in others],el)[:60],flush=True)
# ---- E_0-test with numerically chosen pivots
rg=np.random.default_rng(5); random.seed(5)
def ev(q,vals):
    sm=0
    for k,v in q.items():
        t=complex(v)
        for e,x in zip(k,vals): t*=x**e
        sm+=t
    return sm
cells=[(i,j) for i in range(4) for j in range(5)]
pivsets=[]
for ps in range(npiv):
    vals=[complex(rg.normal(),rg.normal()) for _ in names]
    A=np.array([[ev(E[i][j],vals) if E[i][j] else 0 for (i,j) in cells] for E in span])
    order=list(range(len(span))); random.shuffle(order); rows=[]
    for k in order:
        if np.linalg.matrix_rank(A[rows+[k]],tol=1e-8)>len(rows): rows.append(k)
    cord=list(range(20)); random.shuffle(cord); cols=[]
    for c_ in cord:
        if np.linalg.matrix_rank(A[rows][:,cols+[c_]],tol=1e-8)>len(cols): cols.append(c_)
        if len(cols)==len(rows): break
    pivsets.append((rows,cols))
print('dim(M + C d) =',len(pivsets[0][0]),'pivot sets:',[[('x%d%d'%cells[c]) for c in cols] for rows,cols in pivsets],flush=True)
dets=[]
for (rows,cols) in pivsets:
    mat='matrix PM[%d][%d];\n'%(len(rows),len(cols))
    for a,k in enumerate(rows):
        for b,c_ in enumerate(cols):
            q=span[k][cells[c_][0]][cells[c_][1]]
            if q: mat+='PM[%d,%d]=%s;\n'%(a+1,b+1,strq(q))
    out=sing(['z'],body=mat+'poly dd=det(PM);\nprint(dd);')
    dets.append(out.replace(' ',''))
print('pivot determinants computed (lengths %s)'%[len(x) for x in dets],flush=True)
cov=sing(rels+['('+x+')' for x in dets]+['z'],body='ideal G=std(I);\nif(G[1]==1){print("COVERED");}else{LIB "primdec.lib";print(minAssGTZ(G));}')
print('pivot sets cover the family (ideal(Delta_i, relations) = 1):',cov,flush=True)
e0_ok=True
for (rows,cols),dl in zip(pivsets,dets):
    zero=[W('x%d%d'%cells[c_]) for c_ in cols]; free=[('x%d%d'%cells[c_]) for c_ in range(20) if c_ not in cols]
    res={}
    for xn in free:
        out=sing(rels+F.fo+[W(r) for r in F.rv]+zero+['z*('+dl+')-1',F.eq(xn,1)],el); res.setdefault(out.strip()=='1',[]).append(xn)
    e0_ok=e0_ok and not res.get(False)
    print('  E_0-test pivot set %s: unit in %d charts, NON-unit in %s'%([('x%d%d'%cells[c_]) for c_ in cols],len(res.get(True,[])),res.get(False,[])),flush=True)
print('VERDICT %s: Omega-test %s, E_0-test %s, coverage %s'%(fam+' '+defo,'UNIT' if om_ok else 'NOT unit','UNIT' if e0_ok else 'NOT unit',cov[:20]))
