# substitute the conic parametrisation x(s) for b (rel01) or for c (rel02) and write a Singular script solving for the other vector
import sys, sympy as sp
which=sys.argv[1]   # g1: b = x(s) in rel01 ; g2: c = x(s) in rel02
s,w,b2,b3,c2,c3=sp.symbols('s w b2 b3 c2 c3')
x=[sp.sympify(e) for e in open('/home/kevxhk/work/L-gct-210/reg2/g2/xs.txt').read().split(';')]
rel=open('/home/kevxhk/work/L-gct-210/reg2/g2/rel01.txt' if which=='g1' else '/home/kevxhk/work/L-gct-210/reg2/g2/rel02.txt').read().strip().split(';')
if which=='g1': sub={b2:x[1]/x[0],b3:x[2]/x[0]}; keep=(c2,c3)
else: sub={c2:x[1]/x[0],c3:x[2]/x[0]}; keep=(b2,b3)
out=[]
for g in rel:
    e=sp.together(sp.sympify(g).subs(sub)); n=sp.numer(e); n=sp.rem(sp.expand(n),w**2+w+1,w)
    if n!=0: out.append(str(sp.expand(n)).replace('**','^'))
v=' ,'.join(str(k) for k in keep)
open('/home/kevxhk/work/L-gct-210/reg2/g2/%s_solve.sing'%which,'w').write('ring S=(0,w),(%s,s),lp; minpoly=w^2+w+1;\nideal K=%s;\npoly x0=%s;\nK=sat(K,x0);\nK=std(K);\nprint(dim(K));\nprint(K);\nquit;\n'%(v,','.join(out),str(x[0]).replace('**','^')))
