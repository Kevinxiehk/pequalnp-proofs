# Round 16: TWO-STAGE e = 5 type solver.  Stage 1: the 5-dim line configuration (pattern + incidence class) -> prime components (Singular minAssGTZ,
# cached).  Stage 2: for each component, add the genuine element G (row pair: x, y in C^5; column pair: x, y in C^4), ALL level equations of the
# 6 elements, the sums (R1/C1), and saturate by the genuineness of G (R1/C1: x != 0, y != 0; N: sum x != 0).  Verdict per (type, class):
# KILLED-P2 / KILLED-P1 / LINES EMPTY / EMPTY / NONEMPTY / TIMEOUT.   usage: twostage.py A B KIND P Q GTYPE [TMO]
import sys, subprocess, itertools, os, json, hashlib; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
A=[int(c) for c in sys.argv[1]]; Bd=[int(c) for c in sys.argv[2]]; kind=sys.argv[3]; P=int(sys.argv[4]); Q=int(sys.argv[5]); gt=sys.argv[6]
TMO=int(sys.argv[7]) if len(sys.argv)>7 else 120
CACHE='/home/kevxhk/work/L-gct-210/reg2/e5/cache'; os.makedirs(CACHE,exist_ok=True)
rows=[i for i in range(4) if A[i]]; cols=[c for c in range(5) if Bd[c]]; nr,nc=len(rows),len(cols)
def orth_ok(dims,n):
    dims=sorted([d for d in dims if d],reverse=True)
    if len(dims)<2: return True
    if n==4 and dims[0]==3 and dims[1]>=2: return False
    if n==3 and dims[0]==3: return False
    if n==3 and dims[0]==2 and dims[1]==2: return False
    return True
tag='TYPE %s|%s %s(%d,%d) %s'%(sys.argv[1],sys.argv[2],kind,P,Q,gt)
if not orth_ok(A,4) or not orth_ok(Bd,3): print(tag+': KILLED-P2'); sys.exit()
def ok_rp(p): return all(A[p[i]]==A[i] for i in range(4)) and (kind!='row' or {p[P],p[Q]}=={P,Q})
def ok_cp(q): return all(Bd[q[c]]==Bd[c] for c in range(5)) and (kind!='col' or {q[P],q[Q]}=={P,Q})
RP=[p for p in itertools.permutations(range(4)) if ok_rp(p)]; CP=[q for q in itertools.permutations(range(5)) if ok_cp(q)]
def canon(bits):
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    return min(tuple(S[(p[r],q[c])] for r in rows for c in cols) for p in RP for q in CP)
classes=sorted(set(canon(b) for b in itertools.product([0,1],repeat=nr*nc))) if nr*nc else [()]
def sing(body,tmo):
    fn='/tmp/twostage_%d.sing'%os.getpid(); open(fn,'w').write(body)
    try: r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(fn),capture_output=True,text=True,timeout=tmo)
    except subprocess.TimeoutExpired: return None
    return '\n'.join(l for l in r.stdout.split('\n') if not l.startswith('// **'))
def minors_of(part):
    k=len(part); Ln=len(part[0]); mins=[]
    for cs in itertools.combinations(range(Ln),k):
        M_=[[part[a_][b_] or '0' for b_ in cs] for a_ in range(k)]; terms=[]
        for perm in itertools.permutations(range(k)):
            if any(M_[a_][perm[a_]]=='0' for a_ in range(k)): continue
            sg=1
            for a_ in range(k):
                for b_ in range(a_+1,k):
                    if perm[a_]>perm[b_]: sg=-sg
            terms.append(('+' if sg>0 else '-')+'*'.join(M_[a_][perm[a_]] for a_ in range(k)))
        if terms:
            ex=''.join(terms); ex=ex[1:] if ex.startswith('+') else '0'+ex; mins.append('('+ex+')')
    return ','.join(mins)
def lines_of(S):
    rowel=[]; colel=[]; params=[]
    for r in rows:
        for k in range(A[r]):
            v=[None if (c in cols and S[(r,c)]==0) else 'r%d%d%d'%(r,k,c) for c in range(5)]; rowel.append((r,v)); params+=[x for x in v if x]
    for c in cols:
        for k in range(Bd[c]):
            v=[None if (i in rows and S[(i,c)]==1) else 'c%d%d%d'%(c,k,i) for i in range(4)]; colel.append((c,v)); params+=[x for x in v if x]
    return rowel,colel,params
def elems(R,V,rowel,colel,G=None):
    Bs=[]
    for r,v in rowel:
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for c in range(5): Z[r][c]=V(v[c]) if v[c] else {}
        Bs.append(Z)
    for c,v in colel:
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for i in range(4): Z[i][c]=V(v[i]) if v[i] else {}
        Bs.append(Z)
    if G:
        gx,gy=G; Z=[[{} for _ in range(5)] for _ in range(4)]
        if kind=='row':
            for c in range(5): Z[P][c]=V(gx[c]); Z[Q][c]=V(gy[c])
        else:
            for i in range(4): Z[i][P]=V(gx[i]); Z[i][Q]=V(gy[i])
        Bs.append(Z)
    return Bs
def stage1(bits):
    key=hashlib.md5(('%s|%s|%s'%(sys.argv[1],sys.argv[2],''.join(map(str,bits)))).encode()).hexdigest()
    cf=os.path.join(CACHE,key+'.json')
    if os.path.exists(cf):
        d_=json.load(open(cf))
        if not (d_.get('verdict')=='TIMEOUT-1' and os.environ.get('RETRY_TIMEOUTS')): return d_
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    rowel,colel,params=lines_of(S)
    for (els,idxs) in ((rowel,rows),(colel,cols)):
        for g in idxs:
            part=[v for (ix,v) in els if ix==g]
            if sum(1 for x in part[0] if x)-1<len(part): out={'verdict':'KILLED-P1'}; json.dump(out,open(cf,'w')); return out
    F=Family(params,lambda R,V: elems(R,V,rowel,colel),len(rowel)+len(colel)); np_=len(params)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    lines=[to_str_Q(q,params) for q in lev]+['+'.join(x for x in v if x) for _,v in rowel+colel]
    sats=[minors_of([v for (ix,v) in els if ix==g]) for (els,idxs) in ((rowel,rows),(colel,cols)) for g in idxs]
    body='LIB "elim.lib";\nLIB "primdec.lib";\nring R=0,(%s),dp;\nideal I=%s;\nI=std(I);\n'%(','.join(params),',\n'.join(lines))
    for s_ in sats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("LINES-EMPTY");quit;}\n'%s_
    body+='list L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'
    o=sing(body,TMO)
    if o is None: out={'verdict':'TIMEOUT-1'}
    elif 'LINES-EMPTY' in o: out={'verdict':'LINES-EMPTY'}
    else: out={'verdict':'LINES','comps':[' '.join(c.split()).replace(' ,',',') for c in o.split('COMP')[1:]]}
    json.dump(out,open(cf,'w')); return out
res={}
for bits in classes:
    s1=stage1(bits)
    if s1['verdict']!='LINES': res.setdefault(s1['verdict'],[]).append(''.join(map(str,bits))); continue
    if os.environ.get('STAGE1_ONLY'):
        lin=all(all(len(g.strip())>0 and not any(ch in g for ch in '*^') for g in c.split(',')) for c in s1['comps'])
        res.setdefault('LINES(%d comps,%s)'%(len(s1['comps']),'linear' if lin else 'nonlinear'),[]).append(''.join(map(str,bits))); continue
    S={(rows[i],cols[m]):bits[nc*i+m] for i in range(nr) for m in range(nc)}
    rowel,colel,params=lines_of(S); L=5 if kind=='row' else 4
    gx=['gx%d'%k for k in range(L)]; gy=['gy%d'%k for k in range(L)]; pall=params+gx+gy
    F=Family(pall,lambda R,V: elems(R,V,rowel,colel,(gx,gy)),len(rowel)+len(colel)+1); np_=len(pall)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    gidx=[pall.index(v) for v in gx+gy]
    def gdeg(q): return max(sum(k[i] for i in gidx) for k in q) if q else 0
    lev1=[q for q in lev if gdeg(q)<=1]; lev2=[q for q in lev if gdeg(q)==2]
    glines1=[to_str_Q(q,pall) for q in lev1]+(['+'.join(gx),'+'.join(gy)] if gt in ('R1','C1') else [])
    glines=[to_str_Q(q,pall) for q in lev]+(['+'.join(gx),'+'.join(gy)] if gt in ('R1','C1') else [])
    if gt in ('R1','C1'):
        # round 18 FIX: genuineness MODULO THE GAUGE.  Before: sat by (gx), (gy) only, so G = (row line in P) + (row line in Q) (an element
        # of Lin(M)) passed and every class with lines on both rows came out NONEMPTY.  Now: x not in U_P (span of the lines on line P) and
        # y not in U_Q, i.e. saturate by the maximal minors of [U_P; x] and of [U_Q; y]  (a = 0: the entries of x, as before).
        same_=rowel if kind=='row' else colel
        UP_=[[t or '0' for t in v] for (r_,v) in same_ if r_==P]; UQ_=[[t or '0' for t in v] for (r_,v) in same_ if r_==Q]
        gsats=[minors_of(UP_+[gx]),minors_of(UQ_+[gy])]
    else: gsats=['+'.join(gx)]
    verdicts=[]
    for comp in s1['comps']:
        if os.environ.get('DROPU'):
            # round 19: split by LEMMA 27.1(2).  U' = span of the lines parallel to the pair on the OTHER lines (rows for row kind).  If
            # dim U' = n-1 (n = 5 rows kind / 4 column kind) then z = 0 exactly.  Part A: all equations + z = 0 + genuineness ('A-...');
            # part B: all equations + rank U' <= n-2 (all (n-1)-minors of the U'-matrix) + genuineness ('B-...').  Both EMPTY => EMPTY.
            same_=rowel if kind=='row' else colel; nn=len(gx)
            UO=[[t or '0' for t in v] for (r_,v) in same_ if r_ not in (P,Q)]
            if len(UO)<nn-1: verdicts.append('DROPU-NA'); continue
            mins=[minors_of([UO[i] for i in sub]) for sub in itertools.combinations(range(len(UO)),nn-1)]
            mins=[m for m in mins if m.strip()]
            r1eq=['%s+%s'%(a_,b_) for a_,b_ in zip(gx,gy)]
            out_=[]
            for lab,extra in (('A',r1eq),('B',mins)):
                body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\nif(I[1]==1){print("%s-EMPTY");quit;}\n'%(','.join(pall),comp,',\n'.join(glines+extra),lab)
                for s_ in gsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("%s-EMPTY");quit;}\n'%(s_,lab)
                body+='print("%s-NONEMPTY dim "+string(dim(I)));\nquit;\n'%lab
                o=sing(body,TMO); out_.append('%s-TIMEOUT'%lab if o is None else (o.strip().split('\n')[-1] if o.strip() else '%s-ERR'%lab))
            verdicts.append(' | '.join(out_)); continue
        if os.environ.get('RANK1SPLIT'):
            # round 19: EXACT RANK-ONE SPLIT.  G is rank one mod Lin(M)  <=>  z = x + y lies in U_P + U_Q (then a gauge change gives y = -x).
            # (ii) NON-rank-one part: all equations + saturation by the maximal minors of [U_P; U_Q; z] (+ s != 0 for N); linear equations
            #      first.  'NR1-EMPTY(-LINEAR)' = the rank-one lemma holds on this component (exact).
            # (i)  rank-one part: all equations + y = -x + the usual genuineness saturations ('R1P-...').
            same_=rowel if kind=='row' else colel
            UPQ=[[t or '0' for t in v] for (r_,v) in same_ if r_ in (P,Q)]
            zz=['(%s+%s)'%(a_,b_) for a_,b_ in zip(gx,gy)]
            nsats=([minors_of(UPQ+[zz])] if len(UPQ)+1<=len(gx) else [])+(['+'.join(gx)] if gt=='N' else [])
            if len(UPQ)+1>len(gx): vii='NR1-SKIP'
            else:
                body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\n'%(','.join(pall),comp,',\n'.join(glines1))
                for s_ in nsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("NR1-EMPTY-LINEAR");quit;}\n'%s_
                body+='print("NR1-LINEAR-NONEMPTY");\nquit;\n'
                o=sing(body,TMO)
                if o is not None and 'NR1-EMPTY-LINEAR' in o: vii='NR1-EMPTY-LINEAR'
                else:
                    body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\n'%(','.join(pall),comp,',\n'.join(glines))
                    for s_ in nsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("NR1-EMPTY");quit;}\n'%s_
                    body+='print("NR1-NONEMPTY dim "+string(dim(I)));\nquit;\n'
                    o=sing(body,TMO); vii='NR1-TIMEOUT' if o is None else (o.strip().split('\n')[-1] if o.strip() else 'NR1-ERR')
            r1eq=['%s+%s'%(a_,b_) for a_,b_ in zip(gx,gy)]
            body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\n'%(','.join(pall),comp,',\n'.join(glines+r1eq))
            for s_ in gsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("R1P-EMPTY");quit;}\n'%s_
            body+='print("R1P-NONEMPTY dim "+string(dim(I)));\nquit;\n'
            o=sing(body,TMO); vi='R1P-TIMEOUT' if o is None else (o.strip().split('\n')[-1] if o.strip() else 'R1P-ERR')
            verdicts.append(vii+' | '+vi); continue
        if os.environ.get('RANKDROP'):
            # round 17: restrict to the RANK-DROP locus of the linear system: k random two-sided combinations of the (n_g - gauge)-minors of L
            # (each det(R L Cc) lies in the ideal of (n_g-gamma)-minors by Cauchy-Binet), added to the component; then ALL equations + genuineness.
            import random as _r; _r.seed(11)
            gamma=(A[P]+A[Q]) if kind=='row' else (Bd[P]+Bd[Q]); m_=len(gidx)-gamma
            Lrows=[]
            for q in lev1:
                row=['0']*len(gidx); has=False
                for kk,vv in q.items():
                    if sum(kk[i] for i in gidx)==1:
                        gi=[a for a,i in enumerate(gidx) if kk[i]][0]
                        mon={k2[:]:0 for k2 in []}
                        k3=list(kk); k3[gidx[gi]]=0
                        row[gi]+=' + (%s)'%to_str_Q({tuple(k3):vv},pall); has=True
                if has: Lrows.append(row)
            if gt in ('R1','C1'): Lrows+= [['1' if a<len(gx) else '0' for a in range(len(gidx))],['1' if a>=len(gx) else '0' for a in range(len(gidx))]]
            mat='matrix Lm[%d][%d]=%s;\n'%(len(Lrows),len(gidx),','.join('(%s)'%e for row in Lrows for e in row))
            dets=[]
            for t_ in range(3):
                Rm=[[_r.randint(-3,3) for _ in range(len(Lrows))] for _ in range(m_)]; Cm=[[_r.randint(-3,3) for _ in range(m_)] for _ in range(len(gidx))]
                mat+='matrix R%d[%d][%d]=%s;\nmatrix C%d[%d][%d]=%s;\npoly D%d=det(R%d*Lm*C%d);\n'%(t_,m_,len(Lrows),','.join(str(x) for r_ in Rm for x in r_),t_,len(gidx),m_,','.join(str(x) for r_ in Cm for x in r_),t_,t_,t_)
                dets.append('D%d'%t_)
            body='LIB "elim.lib";\nring R=0,(%s),dp;\n%sideal I=%s,%s,\n%s;\nI=std(I);\n'%(','.join(pall),mat,comp,','.join(dets),',\n'.join(glines))
            for s_ in gsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s_
            body+='print("NONEMPTY dim "+string(dim(I)));\nquit;\n'
            o=sing(body,TMO); verdicts.append('TIMEOUT' if o is None else (o.strip().split('\n')[-1] if o.strip() else 'ERR')); continue
        # round 17: LINEARISED stage 2 -- first only the equations of degree <= 1 in G (P_2-mixed and all degree-1 terms) + sums + genuineness
        body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\n'%(','.join(pall),comp,',\n'.join(glines1))
        for s_ in gsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("EMPTY-LINEAR");quit;}\n'%s_
        body+='print("LINEAR-NONEMPTY");\nquit;\n'
        o=sing(body,TMO)
        if o is not None and 'EMPTY-LINEAR' in o: verdicts.append('EMPTY-LINEAR'); continue
        if os.environ.get('LINEAR_ONLY'): verdicts.append('LIN-TIMEOUT' if o is None else 'LINEAR-NONEMPTY'); continue
        body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s,\n%s;\nI=std(I);\n'%(','.join(pall),comp,',\n'.join(glines))
        for s_ in gsats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s_
        body+='print("NONEMPTY dim "+string(dim(I)));\nquit;\n'
        o=sing(body,TMO); verdicts.append('TIMEOUT' if o is None else (o.strip().split('\n')[-1] if o.strip() else 'ERR'))
    if os.environ.get('DROPU'):
        print('DROPU',tag,''.join(map(str,bits)),verdicts,flush=True)
        verdicts=['EMPTY' if x=='A-EMPTY | B-EMPTY' else x for x in verdicts]
    if os.environ.get('RANK1SPLIT'):
        print('R1SPLIT',tag,''.join(map(str,bits)),verdicts,flush=True)
        verdicts=['EMPTY' if (x.startswith('NR1-EMPTY') and x.endswith('R1P-EMPTY')) else x for x in verdicts]
    v=('EMPTY' if all(x in ('EMPTY','EMPTY-LINEAR') for x in verdicts) else ' / '.join(sorted(set(verdicts))))
    if all(x=='EMPTY-LINEAR' for x in verdicts): v='EMPTY-LINEAR'
    res.setdefault(v,[]).append(''.join(map(str,bits)))
print(tag+': %d classes -> '%len(classes)+'; '.join('%s x%d'%(k,len(v)) for k,v in sorted(res.items())),flush=True)
