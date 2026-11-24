# Round 11, target 3: generic incidence-support split for a line-spanned pattern.  usage: incpat.py ROWDIMS COLDIMS [S|all]
#   ROWDIMS e.g. 111 (rows 0,1,2 have 1-dim parts), COLDIMS e.g. 111 (columns 0,1,2).  P_2 between a row part (row i) and a column part
#   (column m): (column part)[i] * (row part)[m] = 0 for all elements => S[i][m] = 1: the column part vanishes at row i; 0: the row part vanishes
#   at column m.  Ideal: all level equations + sums, saturated by the maximal minors of every part (part of full rank).  Singular over Q.
import sys, subprocess, time, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
rd=[int(ch) for ch in sys.argv[1]]; cd=[int(ch) for ch in sys.argv[2]]; nr=len(rd); nc=len(cd)
def run(S):
    rowel=[]; colel=[]; params=[]
    for i in range(nr):
        for k in range(rd[i]):
            v=[None if (c<nc and S[i][c]==0) else 'r%d%d%d'%(i,k,c) for c in range(5)]; rowel.append((i,v)); params+=[x for x in v if x]
    for m in range(nc):
        for k in range(cd[m]):
            v=[None if (i<nr and S[i][m]==1) else 'c%d%d%d'%(m,k,i) for i in range(4)]; colel.append((m,v)); params+=[x for x in v if x]
    def bfn(R,V):
        Bs=[]
        for i,v in rowel:
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for c in range(5): Z[i][c]=V(v[c]) if v[c] else {}
            Bs.append(Z)
        for m,v in colel:
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for i in range(4): Z[i][m]=V(v[i]) if v[i] else {}
            Bs.append(Z)
        return Bs
    F=Family(params,bfn,len(rowel)+len(colel)); np_=len(params)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    lines=[to_str_Q(q,params) for q in lev]+['+'.join(x for x in v if x) for _,v in rowel+colel if any(v)]
    sats=[]
    for (lab,els,dims) in (('r',rowel,rd),('c',colel,cd)):
        for g in range(len(dims)):
            part=[v for (idx,v) in els if idx==g]
            if not part: continue
            if all(not any(v) for v in part): return 'EMPTY (forced zero part)'
            if sum(1 for x in part[0] if x)-1<len(part): return 'EMPTY (part cannot have full rank: too few free coordinates under sum 0)'
            k=len(part); L=len(part[0])
            mins=[]
            for cols in itertools.combinations(range(L),k):
                M=[[part[a][b] or '0' for b in cols] for a in range(k)]
                if any(all(M[a][b]=='0' for b in range(k)) for a in range(k)) or any(all(M[a][b]=='0' for a in range(k)) for b in range(k)): continue
                terms=[]
                for perm in itertools.permutations(range(k)):
                    if any(M[a][perm[a]]=='0' for a in range(k)): continue
                    sg=1
                    for a in range(k):
                        for b in range(a+1,k):
                            if perm[a]>perm[b]: sg=-sg
                    terms.append(('+' if sg>0 else '-')+'*'.join(M[a][perm[a]] for a in range(k)))
                if terms:
                    ex=''.join(terms); ex=ex[1:] if ex.startswith('+') else '0'+ex
                    mins.append('('+ex+')')
            if not mins: return 'EMPTY (part cannot have full rank)'
            sats.append(','.join(mins))
    body='LIB "elim.lib";\nring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nI=std(I);\n'%(','.join(params),',\n'.join(lines))
    for s in sats: body+='I=sat(I,ideal(%s));\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s
    body+='print("NONEMPTY dim "+string(dim(I)));\n'
    if DUMP: body+='LIB "primdec.lib";\nlist L=minAssGTZ(I);int ii;for(ii=1;ii<=size(L);ii++){print("COMP "+string(ii)+" dim "+string(dim(std(L[ii]))));print(L[ii]);}\n'
    body+='quit;\n'
    _fn='/tmp/incpat_%d.sing'%__import__('os').getpid(); open(_fn,'w').write(body)
    try: r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open(_fn),capture_output=True,text=True,timeout=CASETMO)
    except subprocess.TimeoutExpired: return 'TIMEOUT (%d s)'%CASETMO
    return (r.stdout if DUMP else ' '.join(r.stdout.split())[:100]) or ('ERR '+r.stderr[:200])
mode=sys.argv[3] if len(sys.argv)>3 else 'all'
DUMP=len(sys.argv)>4
import os
CASETMO=int(os.environ.get('CASETMO','120'))
cases=[tuple(int(ch) for ch in mode)] if mode!='all' else list(itertools.product([0,1],repeat=nr*nc))
if mode=='all':      # round 11: only orbit representatives under permutations of rows (resp. columns) with equal part dimensions
    _rp=[p for p in itertools.permutations(range(nr)) if all(rd[p[i]]==rd[i] for i in range(nr))]
    _cp=[q for q in itertools.permutations(range(nc)) if all(cd[q[m]]==cd[m] for m in range(nc))]
    def _canon(b): return min(tuple(b[nc*p[i]+q[m]] for i in range(nr) for m in range(nc)) for p in _rp for q in _cp)
    cases=sorted(set(_canon(b) for b in cases)); print('orbit representatives:',len(cases),flush=True)
res={}
for bits in cases:
    S=[[bits[nc*i+m] for m in range(nc)] for i in range(nr)]
    out=run(S); res.setdefault(out,[]).append(''.join(map(str,bits)))
    if not out.startswith('EMPTY'): print('   case',''.join(map(str,bits)),':',out[:100],flush=True)
for k,v in res.items(): print(k,':',len(v),'cases, e.g.',v[:8])
