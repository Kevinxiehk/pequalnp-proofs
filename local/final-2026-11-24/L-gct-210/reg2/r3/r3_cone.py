# Round 13, R3 (rank-3 three-dim row blocks), cone argument at a FIXED rational point (n, B) for the cases
#   alpha: every zeta_Z constant;   I: zeta_Z in <1, e_4>, n_4 = 0, B(W) in {y_4 = 0};   II: as caseII (n = e3 - e4).
# Rows r = 3 (x = w), j = 0 (y = Bw), k = 1, l = 2.  W = {w : sum w = 0, <n,w> = 0}; B: W -> 1^perp with b skew (+ SK2 constraint of the case),
# chosen as a random rational point of the B-space with rank 3.  Z: z_3 = za*1 + zg*m (m a fixed complement of W in 1^perp), z_1 = p,
# z_2 = zl*1 [+ zk*e_4 in case I] - p, z_0 = q.  Output: a Singular script computing the components of the admissible cone V_B.
# usage: r3_cone.py alpha|I  n0,n1,n2,n3,n4  seed      (writes r3_cone_<case>_<seed>.sing; run it directly with Singular -q)
import sys, random, sympy as sp; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
case=sys.argv[1]; n=[sp.Rational(x) for x in sys.argv[2].split(',')]; seed=int(sys.argv[3]); random.seed(seed)
assert sum(n)==0 and (case!='I' or n[4]==0)
one=sp.Matrix([1]*5); nv=sp.Matrix(n)
Wb=sp.Matrix.hstack(one,nv).T.nullspace(); assert len(Wb)==3           # W = {1,n}^perp (bilinear dot)
F=[sp.Matrix([1 if c==i else (-1 if c==4 else 0) for c in range(5)]) for i in range(4)]
cs=sp.symbols('c0:12'); U=[sum((cs[4*i+k]*F[k] for k in range(4)),sp.zeros(5,1)) for i in range(3)]
eqs=[]
for i in range(3):
    for l in range(i,3):
        eqs.append(sp.expand((Wb[i].T*U[l])[0]+(Wb[l].T*U[i])[0]))
        if case=='I': z=sp.Matrix([0,0,0,0,1]); eqs.append(sp.expand(sum(Wb[i][a]*z[a]*U[l][a]+Wb[l][a]*z[a]*U[i][a] for a in range(5))))
sol=list(sp.linsolve(eqs,cs))[0]; free=sorted(set().union(*[s_.free_symbols for s_ in sol]),key=str)
for tries in range(50):
    val={f:sp.Rational(random.randint(-5,5),random.randint(1,3)) for f in free}
    Bimg=[sum((sp.sympify(sol[4*i+k]).subs(val)*F[k] for k in range(4)),sp.zeros(5,1)) for i in range(3)]
    if sp.Matrix.hstack(*Bimg).rank()==3: break
print('B-space dim',len(free),' chosen B of rank 3:',[list(b.T) for b in Bimg])
# complement m of W in 1^perp
m=next(f for f in F if sp.Matrix.hstack(*Wb,f).rank()==4)
L=[]
for v_ in Wb+Bimg: L+= [sp.lcm([sp.fraction(x)[1] for x in v_])]
zp=['za','zg','p0','p1','p2','p3','p4','zl']+(['zk'] if case=='I' else [])+['q0','q1','q2','q3','q4']
def bfn(R,V):
    c=R.const; Bs=[]
    for i in range(3):
        sc=sp.lcm([sp.fraction(x)[1] for x in list(Wb[i])+list(Bimg[i])])
        Z=[[{} for _ in range(5)] for _ in range(4)]
        Z[3]=[c(int(x*sc)) if x else {} for x in Wb[i]]; Z[0]=[c(int(x*sc)) if x else {} for x in Bimg[i]]; Bs.append(Z)
    Z=[[{} for _ in range(5)] for _ in range(4)]
    Z[3]=[add(V('za'),scal(V('zg'),int(m[k]))) if m[k] else V('za') for k in range(5)]
    Z[1]=[V('p%d'%k) for k in range(5)]
    Z[2]=[add(add(V('zl'),V('zk') if (case=='I' and k==4) else {}),V('p%d'%k),-1) for k in range(5)]
    Z[0]=[V('q%d'%k) for k in range(5)]
    Bs.append(Z); return Bs
Fm=Family(zp,bfn,4); lev=[{k[:len(zp)]:v for k,v in q.items()} for q in Fm.level]; lev=[q for q in lev if q]
lines=[to_str_Q(q,zp) for q in lev]
body=('LIB "elim.lib";\nLIB "primdec.lib";\nring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nI=std(I);\nI=sat(I,ideal(%s));\nI=std(I);\n'
      'print("cone dim "+string(dim(I)));\nif(I[1]==1){print("EMPTY");quit;}\nlist L=minAssGTZ(I);int i;for(i=1;i<=size(L);i++){ideal G=std(L[i]); int nl=0; int k; '
      'for(k=1;k<=size(G);k++){if(deg(G[k])==1){nl++;}} print("COMP "+string(i)+" dim "+string(dim(G))+" degree "+string(mult(G))+" linear forms "+string(nl)); kill G; kill nl; kill k;}\nquit;\n')%(','.join(zp),',\n'.join(lines),','.join(zp))
fn='/home/kevxhk/work/L-gct-210/reg2/r3/r3_cone_%s_%d.sing'%(case,seed); open(fn,'w').write(body); print('written',fn,'level eqs',len(lev))
