import sys, re, subprocess, sympy as sp
src,k,S,ch=sys.argv[1],int(sys.argv[2]),tuple(int(c) for c in sys.argv[3].split(',')),sys.argv[4]
txt=open(src).read(); sg=sp.Symbol('sg'); tau=sp.Symbol('tau')
forms=[sp.Matrix(int(m.group(2)),int(m.group(3)),[sp.sympify(v.strip().replace('^','**'),locals={'sg':sg}) for v in m.group(4).split(',')]) for m in re.finditer(r'matrix F(\d+)\[(\d+)\]\[(\d+)\]=([^;]*);',txt)]
degs=[max([sp.Poly(e,sg).degree() if e!=0 else 0 for e in F]) for F in forms]
forms=[F.applyfunc(lambda e: sp.expand(sp.together(e.subs(sg,1/tau))*tau**d)) for F,d in zip(forms,degs)]
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
fn='/tmp/st2_tau.ms'; out='/tmp/st2_tau.out'
open(fn,'w').write(','.join(str(v) for v in flat+[tau])+'\n'+ch+'\n'+',\n'.join(str(e).replace('**','^') for e in polys)+'\n')
subprocess.run(['msolve','-e',str(len(flat)),'-g','2','-t','1','-f',fn,'-o',out],capture_output=True)
body=[l for l in open(out).read().splitlines() if not l.startswith('#')]
print('tau-chart',S,'char',ch,': first GB elements:',' '.join(body)[:300])
