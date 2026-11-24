# (CC3) last survivors (NOTES-ncol R2.10): case (II-a), mu = l l' of rank 2, |T| = 4, T = {0,1,2,3}, p = 4, m ~ (-c,-c,-c,-c,4c).
# Coordinates z1 = l, z2 = l', z3, z4 on S.  Hatted vectors a^ = a - (A/2)1, beta^ = beta - (B/2)1; a = a^ - (sum a^ / 3) 1 (same for beta).
# Conditions: F3 = e3(a) + e3(beta) == 0 and d3_j = e3(a^(j)) + e3(beta^(j)) proportional to m (d3_t equal for t in T, sum d3 = 2 F3),
# plus the degree-2 normalisation sigma_a sigma_b / 9 = c z1 z2 (lambda = c mu).  Groebner basis over Q of the coefficient equations.
import sympy as sp, itertools, sys
z=sp.symbols('z1:5'); z1,z2,z3,z4=z
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(len(v)),3))
def run(name, ahat, bhat, unknowns, extra):
    sa=sum(ahat); sb=sum(bhat)
    a=[sp.expand(x-sa/3) for x in ahat]; b=[sp.expand(x-sb/3) for x in bhat]
    F3=sp.expand(e3(a)+e3(b))
    d3=[sp.expand(e3([a[k] for k in range(5) if k!=j])+e3([b[k] for k in range(5) if k!=j])) for j in range(5)]
    eqs=list(extra)
    for E in [F3, d3[0]-d3[1], d3[0]-d3[2], d3[0]-d3[3]]:
        eqs+= sp.Poly(E,*z).coeffs()
    eqs=[sp.expand(e) for e in eqs if sp.expand(e)!=0]
    G=sp.groebner(eqs,*unknowns,order='grevlex')
    print(name,': #eqs',len(eqs),' GB =',list(G)[:6],'...' if len(G)>6 else '',flush=True)
    return G
c,k,sa_,sb_=sp.symbols('c k sa sb')
# ---- sub-case (4,0): alpha_t = f_t (t in T), b_t = 0; alpha_p = k z1, b_p = 5c z2/k; pairing f = (z3,-z3,z4,-z4) mod <z1,z2>
u=sp.symbols('u0:8')
f=[z3+u[0]*z1+u[1]*z2, -z3+u[2]*z1+u[3]*z2, z4+u[4]*z1+u[5]*z2, -z4+u[6]*z1+u[7]*z2]
inv=sp.symbols('inv')     # inv = 1/(k c) to forbid k = 0, c = 0
ahat=f+[k*z1]; bhat=[0,0,0,0,sb_*z2]
sa_expr=sp.expand(sum(ahat))
extra=[sp.expand(sb_*k-5*c)]                      # b_p = 5c z2 / k  <=>  sb k = 5c
extra+=sp.Poly(sa_expr-sa_*z1,*z).coeffs()        # sigma_a = sa z1
extra+=[sp.expand(sa_*sb_-9*c), sp.expand(inv*k*c-1)]
run('(4,0)', ahat, bhat, list(u)+[k,c,sa_,sb_,inv], extra)
# ---- sub-case (2,2): alpha_{0,1} = f, b_{2,3} = g, alpha_p, b_p in two orientations
v=sp.symbols('v0:4'); w=sp.symbols('w0:4')
fA=[z3+v[0]*z1+v[1]*z2, -z3+v[2]*z1+v[3]*z2]; gB=[z4+w[0]*z1+w[1]*z2, -z4+w[2]*z1+w[3]*z2]
for orient in (0,1):
    ap = k*z1 if orient==0 else k*z2
    bp = sb_*z2 if orient==0 else sb_*z1          # b_p = 5c * (other factor) / k
    ahat=[fA[0],fA[1],0,0,ap]; bhat=[0,0,gB[0],gB[1],bp]
    extra=[sp.expand(sb_*k-5*c)]
    extra+=sp.Poly(sp.expand(sum(ahat))-sa_*z1,*z).coeffs()      # sigma_a = sa z1  (WLOG sigma_a ~ l = z1)
    sbb=sp.symbols('sbb')
    extra+=sp.Poly(sp.expand(sum(bhat))-sbb*z2,*z).coeffs()      # sigma_b = sbb z2
    extra+=[sp.expand(sa_*sbb-9*c), sp.expand(inv*k*c-1)]
    run('(2,2) orient %d'%orient, ahat, bhat, list(v)+list(w)+[k,c,sa_,sb_,sbb,inv], extra)
