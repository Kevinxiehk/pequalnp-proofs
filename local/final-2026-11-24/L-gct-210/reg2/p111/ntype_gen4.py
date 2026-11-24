# Round 16, target 3: the N type "(1,1|2) + N + R1" with the SUPPORT pattern of ntype1 kept but all values free (chart):
#   row 0 line u0 = (0,1,p1,p2,0), row 3 line u3 = (0,q1,1,q2,0)  [vanish at columns 0, 4],  R1 = e_1 x + e_2 lam x, x = (0,x1,1,x2,0),
#   column-0 plane V = <v1, v2>, v1 = (s1,1,s2,0)-chart ... general: v1 = (v10,v11,v12,v13), v2 = (v20,v21,v22,v23) in echelon chart v11=1,v13=0,v21=0,v23=1,
#   N = e_1 a + e_2 b (a, b in C^5, modulo N -> N + mu R1: chart a2 = 0).
# ALL level equations + sums, saturated by lam, rank V, sum(a) != 0 -> components (dimension = number of free parameters of the type in this chart).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
params=['p1','p2','p4','q1','q2','q4','x1','x2','x4','lam','v10','v12','v20','v22','a0','a1','a3','a4','b0','b1','b2','b3','b4']
def bfn(R,V):
    c=R.const; Bs=[]
    def rowel(i,vec):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(vec); return Z
    Bs.append(rowel(0,[{},c(1),V('p1'),V('p2'),V('p4')])); Bs.append(rowel(3,[{},V('q1'),c(1),V('q2'),V('q4')]))
    x=[{},V('x1'),c(1),V('x2'),V('x4')]; Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1]=list(x); Z[2]=[mul(V('lam'),e) if e else {} for e in x]; Bs.append(Z)
    for vec in ([V('v10'),c(1),V('v12'),{}],[V('v20'),{},V('v22'),c(1)]):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for i in range(4): Z[i][0]=vec[i]
        Bs.append(Z)
    Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1]=[V('a0'),V('a1'),{},V('a3'),V('a4')]; Z[2]=[V('b%d'%k) for k in range(5)]; Bs.append(Z)
    return Bs
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['1+p1+p2+p4','q1+1+q2+q4','x1+1+x2+x4','v10+1+v12','v20+v22+1']
body=('LIB "elim.lib";\nLIB "primdec.lib";\nring R=0,(%s),dp;\nideal I=%s;\nI=std(I);\nI=sat(I,lam);\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\n'
      'I=sat(I,a0+a1+a3+a4);\nI=std(I);\nif(I[1]==1){print("EMPTY");quit;}\nprint("dim "+string(dim(I)));\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP "+string(i)+" dim "+string(dim(std(L[i]))));print(L[i]);}\nquit;\n')%(','.join(params),',\n'.join(lines))
open('/home/kevxhk/work/L-gct-210/reg2/p111/ntype_gen4.sing','w').write(body); print('level equations',len(lev),'vars',len(params))
