# Pattern (2,1,1|2), incidence case (ii), REDUCED parametrisation (reg2 round 3).
#   M(b,c) = e_0 (x) span(5e_0-1, (0,a)) (+) C e_1 (0,b)^T (+) C e_2 (0,c)^T (+) {x e_0^T : x_0 = 0, sum x = 0},
#   b, c in H = {sum-zero vectors of C^4} (columns 1..4), a := cross4(b,c) = signed 3x3 minors of [1;b;c] (a is orthogonal to 1,b,c).
#   Hand classification (NOTES-reg2 section 9): case (ii) = {a,b,c in H nonzero, pairwise orthogonal, T(a,b,c) = sum a_j b_j c_j = 0};
#   component (g): b,c independent -> a ~ cross4(b,c);   component (d): c ~ b isotropic, a ~ cross4(b, b o b)  (mode prefix 'd').
# Charts (S_4 symmetry of the columns 1..4): b_1 = 1; c_1 = 1 or c_2 = 1; a_ja != 0 by Rabinowitsch z*a_ja = 1 (exact over Q: fine).
# Modes: om  : Omega-test  rho_0 = 0, sum_{j>=1} rho_j = 0, rho_jr = 1           (unit for all charts => dim Omega <= 2)
#        e0  : E_0-test    rho = 0, x00=x10=x20=x34=x_{0,ja}=x_{1,jb}=x_{2,jc}=0, x_ib = 1 (unit for all => dim E_0 <= 7)
#        calom / cale0 : calibrations (rho = e_0;  x34 = 1 with the d_0-pivot released): must be NON-unit.
# Output: Singular scripts in /tmp/dr211c/<tag>.sing ; run with run_sing.sh (2 at a time).
import sys, os; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb')
from famtool import *
comp=sys.argv[1]            # 'g' or 'd'
char=int(sys.argv[2]) if len(sys.argv)>2 else 0
od='/tmp/dr211c'; os.makedirs(od,exist_ok=True)
def det3(M):
    return add(add(mul(M[0][0],add(mul(M[1][1],M[2][2]),mul(M[1][2],M[2][1]),-1)),
                   mul(M[0][1],add(mul(M[1][0],M[2][2]),mul(M[1][2],M[2][0]),-1)),-1),
               mul(M[0][2],add(mul(M[1][0],M[2][1]),mul(M[1][1],M[2][0]),-1)))
def cross4(R,b,c):
    one=R.const(1); A=[[one]*4,b,c]; out=[]
    for j in range(4):
        cols=[k for k in range(4) if k!=j]; out.append(scal(det3([[A[i][k] for k in cols] for i in range(3)]),(-1)**j))
    return out
def vec4(R,V,p):
    v=[V(p+'1'),V(p+'2'),V(p+'3')]; v.append(scal(add(add(v[0],v[1]),v[2]),-1)); return v
store={}
def basis(R,V):
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    b=vec4(R,V,'b')
    if comp=='g': cc=vec4(R,V,'c')
    else: cc=b
    a=cross4(R,b,cc if comp=='g' else [mul(x,x) for x in b])
    store['a']=a; store['b']=b; store['c']=cc
    B1=Z(); B1[0][0]=c(4)
    for j in range(1,5): B1[0][j]=c(-1)
    B2=Z(); B3=Z(); B4=Z()
    for j in range(4): B2[0][1+j]=a[j]; B3[1][1+j]=b[j]; B4[2][1+j]=cc[j]
    B5=Z(); B5[1][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
params=['b1','b2','b3']+(['c1','c2','c3'] if comp=='g' else [])+['z']
F=Family(params,basis,6); W=F.W
# re-express a, b, c in the reduced ring (strip y exponents: y's are the first 6 variables of F.R)
strip=lambda q:{k[6:]:v for k,v in q.items()}
A=[strip(q) for q in store['a']]; Bv=[strip(q) for q in store['b']]; Cv=[strip(q) for q in store['c']]
extra_rel=[]
if comp=='d':
    bb={}
    for q in Bv: bb=add(bb,mul(q,q))
    extra_rel=[bb]                       # b isotropic
print('comp %s: level equations %d, FO equations %d'%(comp,len(F.level),len(F.fo)),flush=True)
def write(tag,polys):
    lines=[to_str_Q(q,F.names) for q in polys]; lines=[l for l in lines if l!='0']
    script='ring R=%d,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nprint(size(G));\nprint(G[1]);\nquit;\n'%(char,','.join(F.names),',\n'.join(lines))
    open('%s/%s.sing'%(od,tag),'w').write(script)
cch=[1,2] if comp=='g' else [None]
cnt=0
for jc in cch:
    for ja in range(4):
        base=F.level+extra_rel+[F.eq('b1',1), add(mul(W('z'),A[ja]),F.c(-1))]
        if jc is not None:
            base=base+[add(Cv[jc-1],F.c(-1))]
        jb=1
        jcc=jc if jc is not None else 1
        s=W('r1')
        for j in range(2,5): s=add(s,W('r%d'%j))
        for jr in range(1,5):
            write('%s_om_c%s_a%d_r%d'%(comp,jc,ja+1,jr),base+F.fo+[W('r0'),s,F.eq('r%d'%jr,1)]); cnt+=1
        write('%s_calom_c%s_a%d'%(comp,jc,ja+1),base+F.fo+[F.eq('r0',1)]+[W('r%d'%j) for j in range(1,5)]); cnt+=1
        zero=['x00','x10','x20','x34','x0%d'%(ja+1),'x1%d'%jb,'x2%d'%jcc]
        for xn in [v for v in F.xv if v not in zero]:
            write('%s_e0_c%s_a%d_%s'%(comp,jc,ja+1,xn),base+F.fo+[W(r) for r in F.rv]+[W(v) for v in zero]+[F.eq(xn,1)]); cnt+=1
        write('%s_cale0_c%s_a%d'%(comp,jc,ja+1),base+F.fo+[W(r) for r in F.rv]+[W(v) for v in zero if v!='x34']+[F.eq('x34',1)]); cnt+=1
print('wrote %d scripts to %s'%(cnt,od))
