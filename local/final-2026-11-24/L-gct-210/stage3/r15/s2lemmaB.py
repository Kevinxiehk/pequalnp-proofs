# Round 15: LEMMA S2, non-parallel half, ADAPTED BASIS: b2 = w(t2), b3 = be w(t3) (t2 != t3), e = (1, t2+t3, -2 t2 t3) (chi-coords) spans
# span(b2,b3)^perp, <e,e> = 4 (t2-t3)^2; a = x b2 + y b3 + z e (a basis of V as t2 != t3).  Degree-2 condition becomes z^2 = be (4xy + 3x + 3y + 1),
# so a = 0 is impossible (it would force be = 0): NO a-chart needed.  One system: u be (t2 - t3) = 1.   Usage: s2lemmaB.py P
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r15'); from chilib import line_eqs
P=sys.argv[1]; G=sys.argv[2] if len(sys.argv)>2 else 'slimgb'
w=lambda t,be: ['(%s)'%be,'2*(%s)*(%s)'%(be,t),'-2*(%s)*(%s)^2'%(be,t)]
b2=w('t2','1'); b3=w('t3','be'); e=['1','(t2+t3)','(-2*t2*t3)']
add=lambda *v: ['('+'+'.join(x[k] for x in v)+')' for k in range(3)]
sc=lambda c,v: ['(%s)*(%s)'%(c,x) for x in v]
a=add(sc('x',b2),sc('y',b3),sc('z',e))
Y=[a,a,add(a,b2),add(a,b3),add(sc(-2,a),sc(-1,b2),sc(-1,b3))]
eqs=line_eqs(Y)
s='ring R=%s,(x,y,z,be,t2,t3,u),dp;\noption(redSB);\nideal I=\n%s,\nu*be*(t2-t3)-1;\nint t0=timer;\nideal G=%s(I);\n"S2B neq: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;\nquit;\n'%(P,',\n'.join(eqs),G)
f='/home/kevxhk/work/L-gct-210/stage3/r15/s2B_neq_%s%s.sing'%('p' if P!='0' else 'q','' if G=='slimgb' else '_std'); open(f,'w').write(s); print(f)
