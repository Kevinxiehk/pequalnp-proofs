# For one chart of the parametric FO2-joint system: msolve with elimination order (eliminate the 4*(nq-k) chart variables) -> ideal in sg mod p.
import sys, re, itertools, subprocess, os, sympy as sp
src,k,p,S=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),tuple(int(c) for c in sys.argv[4].split(','))
txt=open(src).read(); sg=sp.Symbol('sg')
forms=[sp.Matrix(int(m.group(2)),int(m.group(3)),[sp.sympify(v.strip().replace('^','**'),locals={'sg':sg}) for v in m.group(4).split(',')]) for m in re.finditer(r'matrix F(\d+)\[(\d+)\]\[(\d+)\]=([^;]*);',txt)]
nq=forms[0].rows; ys=[[sp.Symbol('y%d_%d'%(a,b)) for b in range(nq-k)] for a in range(k)]; flat=[v for r in ys for v in r]
rest=[c for c in range(nq) if c not in S]; L=sp.zeros(k,nq)
for a in range(k):
    L[a,S[a]]=1
    for bi,c in enumerate(rest): L[a,c]=ys[a][bi]
polys=[]
for F in forms:
    P=(L*F*L.T).applyfunc(sp.expand)
    for a in range(k):
        for b in range(a,k):
            if P[a,b]!=0: polys.append(P[a,b])
fn='/tmp/st2_elim.ms'; out='/tmp/st2_elim.out'
open(fn,'w').write(','.join(str(v) for v in flat+[sg])+'\n'+str(p)+'\n'+',\n'.join(str(e).replace('**','^') for e in polys)+'\n')
subprocess.run(['msolve','-e',str(len(flat)),'-g','2','-t','1','-f',fn,'-o',out],capture_output=True)
res=open(out).read(); body=[l for l in res.splitlines() if not l.startswith('#')]
print('chart',S,'elimination output (polys in sg only):'); print('\n'.join(body)[:1500])
