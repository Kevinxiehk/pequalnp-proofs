# Round 13: (2,2,1|1), incidence class 110, after the rigorous reduction (NOTES-reg2 21.2):  x ~ (0,0,1,-1) in column 0; U_0 cap U_1 != 0.
#  case A: U_0 = U_1 = T = <a, v> (totally isotropic), u_2 = a;   case B: U_0 = <a,p>, U_1 = <a,q>, u_2 = a.
#  In both cases a is isotropic, sum 0, a_0 = 0 and sum a^3 = 0 (P_3 on rows 0,1,2), so a_1..a_4 have power sums p1 = p2 = p3 = 0, i.e. they
#  are c*(1,i,-1,-i) up to the order of columns 1..4 (S_4): a = (0,1,I,-1,-I), I^2 + 1 = 0.  ALL level equations (famtool) + I^2+1, saturated by
#  the 2x2 minors of the parts.  usage: hand221_110.py A|B  -> writes hand221_110_<case>.sing
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
case=sys.argv[1]
if case=='A': params=['I']+['v%d'%k for k in range(5)]
else: params=['I']+['p%d'%k for k in range(5)]+['q%d'%k for k in range(5)]
def bfn(R,V):
    c=R.const; I=V('I'); a=[{},c(1),I,c(-1),scal(I,-1)]; Bs=[]
    def rowel(i,w):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(w); return Z
    if case=='A':
        v=[V('v%d'%k) for k in range(5)]
        Bs=[rowel(0,a),rowel(0,v),rowel(1,a),rowel(1,v),rowel(2,a)]
    else:
        p=[V('p%d'%k) for k in range(5)]; q=[V('q%d'%k) for k in range(5)]
        Bs=[rowel(0,a),rowel(0,p),rowel(1,a),rowel(1,q),rowel(2,a)]
    Z=[[{} for _ in range(5)] for _ in range(4)]; Z[2][0]=c(1); Z[3][0]=c(-1); Bs.append(Z)
    return Bs
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['I^2+1']
if case=='A':
    lines.append('v0+v1+v2+v3+v4'); mats='matrix A[2][5]=0,1,I,-1,-I,v0,v1,v2,v3,v4;'; sats=['minor(A,2)']
else:
    lines+=['p0+p1+p2+p3+p4','q0+q1+q2+q3+q4']; mats='matrix A[2][5]=0,1,I,-1,-I,p0,p1,p2,p3,p4; matrix Bq[2][5]=0,1,I,-1,-I,q0,q1,q2,q3,q4;'; sats=['minor(A,2)','minor(Bq,2)']
body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I0=%s;\n%s\nideal J=std(I0);\n'%(','.join(params),',\n'.join(lines),mats)
for s_ in sats: body+='J=sat(J,%s);\nJ=std(J);\nif(J[1]==1){print("case %s: EMPTY");quit;}\n'%(s_,case)
body+='print("case %s: NONEMPTY dim "+string(dim(J)));\nLIB "primdec.lib";\nprint(minAssGTZ(J));\nquit;\n'%case
open('/home/kevxhk/work/L-gct-210/reg2/p111/hand221_110_%s.sing'%case,'w').write(body); print('case',case,'level equations',len(lev))
