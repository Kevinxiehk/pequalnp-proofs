# Round 13: (2,1,1,1|1), incidence class 1001, after the rigorous reduction (NOTES-reg2 21.3).  x ~ (0,1,-1,0) in column 0; u_1, u_2 vanish at
# column 0; u_1, u_2, u_3 lie in U' = U_0^perp cap 1^perp and are pairwise orthogonal.  Remaining sub-cases (the others are excluded by hand):
#   D1b: U_0 = <u1,u2> (u1, u2 independent), u3 = g1 u1 + g2 u2;   D1c: u2 ~ u1, U_0 = <u1,u3>;
#   D2s3: u1 ~ u2 ~ r, U_0 = <r,w>, u3 = u (free);   D2s1: u2 ~ u3 ~ r, U_0 = <r,w>, u1 = u (u_0 = 0);   r = (0,1,I,-1,-I), I^2 = -1
#   (r isotropic, sum r^3 = 0, r_0 = 0 => r_1..r_4 are c*(1,i,-1,-i) up to the order of columns 1..4).
# ALL level equations (famtool) + sums (+ I^2+1), saturated by the nondegeneracy minors.  usage: hand2111_1001.py D1b|D1c|D2s3|D2s1
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
case=sys.argv[1]
vec=lambda nm,zero0=False: [None if (zero0 and k==0) else '%s%d'%(nm,k) for k in range(5)]
spec={'D1b':dict(vars=dict(a=vec('a',True),b=vec('b',True)),extra=['g1','g2']),
      'D1c':dict(vars=dict(a=vec('a',True),b=vec('b')),extra=[]),
      'D2s3':dict(vars=dict(w=vec('w'),u=vec('u')),extra=['I']),
      'D2s1':dict(vars=dict(w=vec('w'),u=vec('u',True)),extra=['I'])}[case]
params=[x for v in spec['vars'].values() for x in v if x]+spec['extra']
def bfn(R,V):
    c=R.const
    def P(nm): return [V(x) if x else {} for x in spec['vars'][nm]]
    def rowel(i,w):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(w); return Z
    if case=='D1b':
        a=P('a'); b=P('b'); u3=[add(mul(V('g1'),a[k]) if a[k] else {},mul(V('g2'),b[k]) if b[k] else {}) for k in range(5)]
        Bs=[rowel(0,a),rowel(0,b),rowel(1,a),rowel(2,b),rowel(3,u3)]
    elif case=='D1c':
        a=P('a'); b=P('b'); Bs=[rowel(0,a),rowel(0,b),rowel(1,a),rowel(2,a),rowel(3,b)]
    else:
        I=V('I'); r=[{},c(1),I,c(-1),scal(I,-1)]; w=P('w'); u=P('u')
        Bs=[rowel(0,r),rowel(0,w)]+([rowel(1,r),rowel(2,r),rowel(3,u)] if case=='D2s3' else [rowel(1,u),rowel(2,r),rowel(3,r)])
    Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1][0]=c(1); Z[2][0]=c(-1); Bs.append(Z)
    return Bs
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['+'.join(x for x in v if x) for v in spec['vars'].values()]
row=lambda nm:','.join(x or '0' for x in spec['vars'][nm])
if case=='D1b': mats='matrix A[2][5]=%s,%s;'%(row('a'),row('b')); sats=['minor(A,2)','ideal(g1,g2)']
elif case=='D1c': mats='matrix A[2][5]=%s,%s;'%(row('a'),row('b')); sats=['minor(A,2)']
else:
    lines.append('I^2+1'); mats='matrix A[2][5]=0,1,I,-1,-I,%s; matrix Bu[2][5]=0,1,I,-1,-I,%s;'%(row('w'),row('u')); sats=['minor(A,2)','minor(Bu,2)']
body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I0=%s;\n%s\nideal J=std(I0);\n'%(','.join(params),',\n'.join(lines),mats)
for s_ in sats: body+='J=sat(J,%s);\nJ=std(J);\nif(J[1]==1){print("case %s: EMPTY");quit;}\n'%(s_,case)
body+='print("case %s: NONEMPTY dim "+string(dim(J)));\nquit;\n'%case
open('/home/kevxhk/work/L-gct-210/reg2/p111/hand2111_1001_%s.sing'%case,'w').write(body); print('case',case,'vars',len(params),'level equations',len(lev))
