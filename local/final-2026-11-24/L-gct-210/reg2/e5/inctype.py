# Round 16, target 1: AUTOMATIC e = 5 TYPE SOLVER.  Type = line pattern (a_0>=..>=a_3 | b_0>=..>=b_4), parts <= 3, sum 5, + ONE genuine element
# G on a row pair {r,j} (R1: sum x = sum y = 0; N: sum x != 0) or a column pair {c,d} (C1 / N).  For every incidence class S (row part i vs
# column part m: the column part vanishes at row i, or the row part vanishes at column m), orbit-reduced:
#   PRE-CHECKS (no Groebner basis): (P1) a part forced to zero or below its dimension by the incidences + sum condition (as incpat);
#     (P2) ORTHOGONALITY: pairwise orthogonal row parts inside V = 1^perp (dim 4) / column parts inside 1^perp of C^4 (dim 3) with impossible
#     dimensions: dims d1 >= d2 with d2 > n - d1 + min(d2, isotropic bound) -- concretely, for rows: (3, >=2) impossible; for columns: a 3-dim
#     part together with any other column part, and (2, 2), impossible (19.x/21.1 (O1)-(O3));
#   GB: all level equations (famtool) + sums, saturated by the maximal minors of every part and by the genuineness of G
#     (R1/C1: x != 0 and y != 0; N: sum x != 0).
# usage: inctype.py A B KIND P Q GTYPE [CASETMO]   e.g.  inctype.py 2100 20000 row 0 2 R1       (A = row dims, B = column dims, as digits)
import sys, subprocess, itertools, os; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
A=[int(c) for c in sys.argv[1]]; Bd=[int(c) for c in sys.argv[2]]; kind=sys.argv[3]; P=int(sys.argv[4]); Q=int(sys.argv[5]); gt=sys.argv[6]
CASETMO=int(sys.argv[7]) if len(sys.argv)>7 else 60
rows=[i for i in range(4) if A[i]]; cols=[c for c in range(5) if Bd[c]]
def orth_ok(dims,n):
    dims=sorted([d for d in dims if d],reverse=True)
    if len(dims)<2: return True
    if n==4 and dims[0]==3 and dims[1]>=2: return False
    if n==3 and dims[0]==3: return False
    if n==3 and dims[0]==2 and dims[1]==2: return False
    return True
if not orth_ok(A,4) or not orth_ok(Bd,3): print('TYPE %s|%s %s(%d,%d) %s: KILLED (P2 orthogonality of the line parts)'%(sys.argv[1],sys.argv[2],kind,P,Q,gt)); sys.exit()
nr,nc=len(rows),len(cols)
# symmetries preserving the type: row perms fixing the dims and the genuine pair (as a set), column perms likewise
def ok_rp(p):
    if any(A[p[i]]!=A[i] for i in range(4)): return False
    if kind=='row' and {p[P],p[Q]}!={P,Q}: return False
    return True
def ok_cp(q):
    if any(Bd[q[c]]!=Bd[c] for c in range(5)): return False
    if kind=='col' and {q[P],q[Q]}!={P,Q}: return False
    return True
RP=[p for p in itertools.permutations(range(4)) if ok_rp(p)]; CP=[q for q in itertools.permutations(range(5)) if ok_cp(q)]
def canon(bits):
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    best=None
    for p in RP:
        for q in CP:
            t=tuple(S[(p[r],q[c])] for r in rows for c in cols)
            best=t if best is None or t<best else best
    return best
classes=sorted(set(canon(b) for b in itertools.product([0,1],repeat=nr*nc))) if nr*nc else [()]
res={}
def run(bits):
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    params=[]; rowel=[]; colel=[]
    for r in rows:
        for k in range(A[r]):
            v=[None if (c in cols and S[(r,c)]==0) else 'r%d%d%d'%(r,k,c) for c in range(5)]; rowel.append((r,v)); params+=[x for x in v if x]
    for c in cols:
        for k in range(Bd[c]):
            v=[None if (i in rows and S[(i,c)]==1) else 'c%d%d%d'%(c,k,i) for i in range(4)]; colel.append((c,v)); params+=[x for x in v if x]
    L=5 if kind=='row' else 4
    gx=['gx%d'%k for k in range(L)]; gy=['gy%d'%k for k in range(L)]; params+=gx+gy
    # (P1) pre-check on parts
    for (lab,els,dims,idxs) in (('r',rowel,A,rows),('c',colel,Bd,cols)):
        for g in idxs:
            part=[v for (ix,v) in els if ix==g]
            if sum(1 for x in part[0] if x)-1<len(part): return 'KILLED (P1 incidence)'
    if os.environ.get('PRECHECK_ONLY'): return 'SURVIVES PRE-CHECK'
    def bfn(R,V):
        Bs=[]
        for r,v in rowel:
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for c in range(5): Z[r][c]=V(v[c]) if v[c] else {}
            Bs.append(Z)
        for c,v in colel:
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for i in range(4): Z[i][c]=V(v[i]) if v[i] else {}
            Bs.append(Z)
        Z=[[{} for _ in range(5)] for _ in range(4)]
        if kind=='row':
            for c in range(5): Z[P][c]=V(gx[c]); Z[Q][c]=V(gy[c])
        else:
            for i in range(4): Z[i][P]=V(gx[i]); Z[i][Q]=V(gy[i])
        Bs.append(Z); return Bs
    F=Family(params,bfn,len(rowel)+len(colel)+1); np_=len(params)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    lines=[to_str_Q(q,params) for q in lev]+['+'.join(x for x in v if x) for _,v in rowel+colel]
    if gt in ('R1','C1'): lines+=['+'.join(gx),'+'.join(gy)]
    sats=[]
    for (els,idxs) in ((rowel,rows),(colel,cols)):
        for g in idxs:
            part=[v for (ix,v) in els if ix==g]; k=len(part); Ln=len(part[0]); mins=[]
            for cs in itertools.combinations(range(Ln),k):
                M_=[[part[a_][b_] or '0' for b_ in cs] for a_ in range(k)]
                terms=[]
                for perm in itertools.permutations(range(k)):
                    if any(M_[a_][perm[a_]]=='0' for a_ in range(k)): continue
                    sg=1
                    for a_ in range(k):
                        for b_ in range(a_+1,k):
                            if perm[a_]>perm[b_]: sg=-sg
                    terms.append(('+' if sg>0 else '-')+'*'.join(M_[a_][perm[a_]] for a_ in range(k)))
                if terms:
                    ex=''.join(terms); ex=ex[1:] if ex.startswith('+') else '0'+ex; mins.append('('+ex+')')
            sats.append(','.join(mins))
    if gt in ('R1','C1'): sats+=[','.join(gx),','.join(gy)]
    else: sats.append('+'.join(gx))
    body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s;\nI=std(I);\n'%(','.join(params),',\n'.join(lines))
    for s_ in sats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s_
    body+='print("NONEMPTY dim "+string(dim(I)));\nquit;\n'
    fn='/tmp/inctype_%d.sing'%os.getpid(); open(fn,'w').write(body)
    try: r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=CASETMO)
    except subprocess.TimeoutExpired: return 'TIMEOUT'
    out=' '.join(l for l in r.stdout.split('\n') if not l.startswith('// **')).strip()
    return out[:60] or ('ERR '+r.stderr[:100])
for bits in classes:
    o=run(bits); res.setdefault(o,[]).append(''.join(map(str,bits)))
print('TYPE %s|%s %s(%d,%d) %s: %d classes -> '%(sys.argv[1],sys.argv[2],kind,P,Q,gt,len(classes))+'; '.join('%s x%d'%(k,len(v)) for k,v in sorted(res.items())),flush=True)
