# CALIBRATION of inc111.py: the same machinery on the pattern (2,1,1|1,1) (8 CE-1 hits): row 0: u0, u0' (2-dim part), rows 1, 2: u1, u2;
# columns 0, 1: x0, x1.  S[i][m] = 1: x_m[i] = 0, else the row-i part vanishes at column m.  Nondegeneracy: saturate by the coordinates of
# u1, u2, x0, x1 and by the 2x2 minors of [u0; u0'].  Expect NON-EMPTY classes.
import sys, subprocess, time, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
def run(bits):
    S=[[bits[2*i+m] for m in range(2)] for i in range(3)]
    rowsel=[0,0,1,2]; names=['a','b','c','d']
    U=[[None if (c<2 and S[rowsel[k]][c]==0) else '%s%d'%(names[k],c) for c in range(5)] for k in range(4)]
    X=[[None if (i<3 and S[i][m]==1) else 'x%d%d'%(m,i) for i in range(4)] for m in range(2)]
    params=[v for row in U for v in row if v]+[v for row in X for v in row if v]
    def bfn(R,V):
        Bs=[]
        for k in range(4):
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for c in range(5): Z[rowsel[k]][c]=V(U[k][c]) if U[k][c] else {}
            Bs.append(Z)
        for m in range(2):
            Z=[[{} for _ in range(5)] for _ in range(4)]
            for i in range(4): Z[i][m]=V(X[m][i]) if X[m][i] else {}
            Bs.append(Z)
        return Bs
    F=Family(params,bfn,6); np_=len(params)
    lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
    lines=[to_str_Q(q,params) for q in lev]
    for row in U+X: lines.append('+'.join(v for v in row if v) or '0')
    lines=[l for l in lines if l!='0']
    sats=[','.join(v for v in row if v) for row in U[2:]+X]
    if any(s=='' for s in sats): return 'EMPTY (forced zero vector)'
    a=[U[0][c] or '0' for c in range(5)]; b=[U[1][c] or '0' for c in range(5)]
    minors=','.join('(%s)*(%s)-(%s)*(%s)'%(a[p],b[q],a[q],b[p]) for p,q in itertools.combinations(range(5),2))
    body='LIB "elim.lib";\nring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nI=std(I);\n'%(','.join(params),',\n'.join(lines))
    for s in sats+[minors]: body+='I=sat(I,ideal(%s));\nif(typeof(I)=="list"){I=I[1];}\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'%s
    body+='print("dim "+string(dim(I)));\nquit;\n'
    open('/tmp/cal211.sing','w').write(body)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/cal211.sing'),capture_output=True,text=True,timeout=600)
    return ' '.join(r.stdout.split())[:120]
res={}
for bits in itertools.product([0,1],repeat=6):
    out=run(bits); res.setdefault(out.split(' (')[0],[]).append(''.join(map(str,bits)))
for k,v in res.items(): print(k,':',len(v),'cases, e.g.',v[:6])
