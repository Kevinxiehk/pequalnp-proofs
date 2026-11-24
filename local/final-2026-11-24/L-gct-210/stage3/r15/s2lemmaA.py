# Round 15: LEMMA S2, non-parallel half, alternative normalisation: a-chart a_k = 1 (k = 1,2,3; a != 0), b2 = b2s w(t2), b3 = b3s w(t3),
# u b2s b3s (t2 - t3) = 1. (Same statement as s2lemma.py 'neq'; one variable fewer.)  Usage: s2lemmaA.py K P
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r15'); from chilib import line_eqs
K,P=int(sys.argv[1]),sys.argv[2]
a=['a1','a2','a3']; a[K-1]='1'
w=lambda t,be: ['(%s)'%be,'2*(%s)*(%s)'%(be,t),'-2*(%s)*(%s)^2'%(be,t)]
b2=w('t2','b2s'); b3=w('t3','b3s')
add=lambda *v: ['('+'+'.join(x[k] for x in v)+')' for k in range(3)]
sc=lambda c,v: ['(%s)*(%s)'%(c,x) for x in v]
Y=[a,a,add(a,b2),add(a,b3),add(sc(-2,a),sc(-1,b2),sc(-1,b3))]
eqs=line_eqs(Y)
vs=','.join([x for x in ['a1','a2','a3'] if x!='a%d'%K]+['b2s','t2','b3s','t3','u'])
s='ring R=%s,(%s),dp;\noption(redSB);\nideal I=\n%s,\nu*b2s*b3s*(t2-t3)-1;\nint t0=timer;\nideal G=slimgb(I);\n"S2A neq chart %d: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;\nquit;\n'%(P,vs,',\n'.join(eqs),K)
f='/home/kevxhk/work/L-gct-210/stage3/r15/s2A_neq%d_%s.sing'%(K,'p' if P!='0' else 'q'); open(f,'w').write(s); print(f)
