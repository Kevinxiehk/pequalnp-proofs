# verify2 r16/r17: INDEPENDENT incidence split for the line pattern (1,1,1|1,1,1) (reg2 19.4). 4x5 matrices; row lines e_i (x) u_i (rows 0,1,2,
# u_i in C^5, sum 0), column lines x_m (x) e_m^T (columns 0,1,2, x_m in C^4, sum 0). Mixed P_2: x_m[i] u_i[m] = 0 => per (i,m): S=1 (x_m[i]=0) or S=0 (u_i[m]=0).
# Level: perm_inj(J+Y) = 120 identically in the 6 coefficients. One Singular job per S_3 x S_3 orbit of 3x3 incidence matrices; saturate by each part != 0.
import sympy as sp, itertools, sys
p=sp.symbols('p0:6')
U=[[sp.Symbol('u%d_%d'%(i,j)) for j in range(4)] for i in range(3)]; X=[[sp.Symbol('x%d_%d'%(m,i)) for i in range(3)] for m in range(3)]
u=[U[i]+[-sum(U[i])] for i in range(3)]; x=[X[m]+[-sum(X[m])] for m in range(3)]
Y=sp.zeros(4,5)
for i in range(3):
    for j in range(5): Y[i,j]+=p[i]*u[i][j]
for m in range(3):
    for i in range(4): Y[i,m]+=p[3+m]*x[m][i]
tot=sp.expand(sum(sp.prod([1+Y[i,f[i]] for i in range(4)]) for f in itertools.permutations(range(5),4))-120)
eqs=[e for e in sp.Poly(tot,*p).coeffs() if e!=0]
print('level equations:',len(eqs),file=sys.stderr)
vars_=[v for r in U for v in r]+[v for r in X for v in r]
def subst_zero(i,m,S):  # returns the polynomial that must vanish
    return x[m][i] if S==1 else u[i][m]
# orbit representatives
reps={}
for bits in range(512):
    Mx=[[(bits>>(3*i+m))&1 for m in range(3)] for i in range(3)]
    key=min(tuple(tuple(Mx[a][b] for b in cp) for a in rp) for rp in itertools.permutations(range(3)) for cp in itertools.permutations(range(3)))
    reps.setdefault(key,[]).append(bits)
print('orbits',len(reps),file=sys.stderr)
out=['LIB "elim.lib";','ring R=0,(%s),dp;'%','.join(map(str,vars_)),'option(redSB);','ideal I=%s;'%',\n'.join(str(sp.expand(e)) for e in eqs)]
parts=['ideal(%s)'%','.join(str(c) for c in u[i]) for i in range(3)]+['ideal(%s)'%','.join(str(c) for c in x[m]) for m in range(3)]
for key,members in sorted(reps.items()):
    zs=[str(sp.expand(subst_zero(i,m,key[i][m]))) for i in range(3) for m in range(3)]
    tag=''.join(str(key[i][m]) for i in range(3) for m in range(3))
    out.append('ideal J=I,%s; int t0=timer;'%','.join(zs))
    for q in parts: out.append('J=sat(J,%s);'%q)
    out.append('J=std(J); string v="NONEMPTY"; if(reduce(1,J)==0){v="EMPTY";} printf("class %s (orbit size %d): %%s dim %%s  (%%s s)", v, dim(J), timer-t0); kill J; kill t0; kill v;'%(tag,len(members)))
out.append('quit;')
open('inc111_mine.sing','w').write('\n'.join(out)+'\n'); print('written', file=sys.stderr)
