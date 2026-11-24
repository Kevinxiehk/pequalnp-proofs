# Round 15, target 3: the N-type "(1,1|2) + N + R1" (rows-team seed_t1, t6, clm_s3), with the observed rigid part fixed over Q(w), w^2+w+1 = 0:
#   row 0 line u0 = (0,1,w,w^2,0), row 3 line u3 = (0,w^2,1,w,0) [seed_t1: (0,-.5-.866i,1,-.5+.866i,0) = (0,w^2,1,w,0)],
#   R1 = (e_1 - e_2) (x) x, x = (0,w,1,w^2,0);  unknown: column-0 part V = <v1, v2> (C^4) and N = e_1 a + e_2 b (C^5).
# ALL level equations + w^2+w+1, saturated by rank(v1,v2) = 2 and by sum(a) (N non-sum-zero).  -> ntype.sing (run with Singular -q)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
params=['v%d%d'%(k,i) for k in (1,2) for i in range(4)]+['a%d'%c for c in range(5)]+['b%d'%c for c in range(5)]+['w']
def bfn(R,V):
    c=R.const; w=V('w'); w2=mul(w,w); Bs=[]
    def rowel(i,vec):
        Z=[[{} for _ in range(5)] for _ in range(4)]; Z[i]=list(vec); return Z
    Bs.append(rowel(0,[{},c(1),w,w2,{}])); Bs.append(rowel(3,[{},w2,c(1),w,{}]))
    x=[{},w,c(1),w2,{}]; Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1]=list(x); Z[2]=[scal(e,-1) if e else {} for e in x]; Bs.append(Z)
    for k in (1,2):
        Z=[[{} for _ in range(5)] for _ in range(4)]
        for i in range(4): Z[i][0]=V('v%d%d'%(k,i))
        Bs.append(Z)
    Z=[[{} for _ in range(5)] for _ in range(4)]; Z[1]=[V('a%d'%cc) for cc in range(5)]; Z[2]=[V('b%d'%cc) for cc in range(5)]; Bs.append(Z)
    return Bs
F=Family(params,bfn,6); np_=len(params)
lev=[{k[:np_]:v for k,v in q.items()} for q in F.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,params) for q in lev]+['w^2+w+1','v10+v11+v12+v13','v20+v21+v22+v23']
body='LIB "elim.lib";\nring R=0,(%s),dp;\nideal I=%s;\nmatrix A[2][4]=v10,v11,v12,v13,v20,v21,v22,v23;\nI=std(I);\nI=sat(I,minor(A,2));\nI=std(I);\nif(I[1]==1){print("EMPTY after rank(V)=2");quit;}\nI=sat(I,ideal(a0+a1+a2+a3+a4));\nI=std(I);\nif(I[1]==1){print("EMPTY after sum(a)!=0");quit;}\nprint("NONEMPTY dim "+string(dim(I)));\nLIB "primdec.lib";\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){print("COMP "+string(i)+" dim "+string(dim(std(L[i]))));print(L[i]);}\nquit;\n'%(','.join(params),',\n'.join(lines))
open('/home/kevxhk/work/L-gct-210/reg2/p111/ntype.sing','w').write(body); print('level equations',len(lev),'vars',len(params))
