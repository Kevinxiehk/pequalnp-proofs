# Round 12: pattern (2,2,1,1|) after the orthogonality reduction (NOTES-reg2 20.5).  U_0, U_1 2-dim, u_2, u_3 lines, pairwise orthogonal in
# the nondegenerate 4-dim 1^perp; U_0 cap U_1 = 0 would force u_2 perp 1^perp.  Case A: U_0 = U_1 = T totally isotropic, u_2, u_3 in T^perp = T.
# Case B: U_0 cap U_1 = C a, then u_2, u_3 lie in (U_0+U_1)^perp, a line that is isotropic hence inside rad(U_0+U_1) = C a: u_2 ~ u_3 ~ a.
# Exact level equations (famtool) + saturation by the nondegeneracy minors.  usage: hand2211.py A|B
import sys, subprocess; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
case=sys.argv[1]
if case=='A':
    params=['u%d'%k for k in range(5)]+['v%d'%k for k in range(5)]+['a2','b2','a3','b3']
    def bfn(R,V):
        u=[V('u%d'%k) for k in range(5)]; v=[V('v%d'%k) for k in range(5)]; Bs=[]
        for i in (0,1):
            for w in (u,v):
                Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(w); Bs.append(Z)
        for i,(a,b) in ((2,('a2','b2')),(3,('a3','b3'))):
            Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=[add(mul(V(a),u[k]),mul(V(b),v[k])) for k in range(5)]; Bs.append(Z)
        return Bs
    extra=['u0+u1+u2+u3+u4','v0+v1+v2+v3+v4']
    sats=['minor(matrix([u0,u1,u2,u3,u4],[v0,v1,v2,v3,v4]),2)'.replace('matrix([u0,u1,u2,u3,u4],[v0,v1,v2,v3,v4])','A'),'ideal(a2,b2)','ideal(a3,b3)']
    mat='matrix A[2][5]=u0,u1,u2,u3,u4,v0,v1,v2,v3,v4;'
else:
    params=['a%d'%k for k in range(5)]+['p%d'%k for k in range(5)]+['q%d'%k for k in range(5)]
    def bfn(R,V):
        a=[V('a%d'%k) for k in range(5)]; p=[V('p%d'%k) for k in range(5)]; q=[V('q%d'%k) for k in range(5)]; Bs=[]
        for i,w in ((0,a),(0,p),(1,a),(1,q),(2,a),(3,a)):
            Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(w); Bs.append(Z)
        return Bs
    extra=['a0+a1+a2+a3+a4','p0+p1+p2+p3+p4','q0+q1+q2+q3+q4']
    sats=['minor(A,2)','minor(Bq,2)']
    mat='matrix A[2][5]=a0,a1,a2,a3,a4,p0,p1,p2,p3,p4; matrix Bq[2][5]=a0,a1,a2,a3,a4,q0,q1,q2,q3,q4;'
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+extra
body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s;\n%s\nI=std(I);\n'%(','.join(params),',\n'.join(lines),mat)
for s_ in sats: body+='I=sat(I,%s);\nI=std(I);\nif(I[1]==1){print("case %s: EMPTY");quit;}\n'%(s_,case)
body+='print("case %s: NONEMPTY dim "+string(dim(I)));\nquit;\n'%case
fn='/home/kevxhk/work/L-gct-210/reg2/p111/hand2211_%s.sing'%case; open(fn,'w').write(body); print('level equations',len(lev))
