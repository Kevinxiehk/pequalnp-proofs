# verify2 r12: HAND LEMMA check -- (alpha0), |supp W| = 3 dies at degree 2: with A_j = n_j (x) phi_j (P_1 = 0), n_0 = n_1 = n_2 ~ v (W = v l^T),
# M = sum_{j<=3} A_j = v (x) psi + n_3 (x) phi_3, the degree-2 condition A_4^*A_4 = 5 (A_4 = -3 - M) reads s^T (4 + 3(M + M^T) + M^T M) s = 0 on V.
# Claim: no psi, phi_3 in V for ANY isotropic v, n_3 (v, n_3 nonzero).  Check: Singular over Q(i), v = w(t0), n3 = w(t3) or chi_3 (t = infinity).
import sympy as sp, itertools, subprocess
I=sp.I
chi=[[I**(k*r) for r in range(4)] for k in range(4)]
t0,t3=sp.symbols('t0 t3'); p=sp.symbols('p0:3'); f=sp.symbols('f0:3'); s=sp.symbols('s0:3')
w=lambda t:[chi[1][r]+2*t*chi[2][r]-2*t**2*chi[3][r] for r in range(4)]
vecV=lambda c:[c[0],c[1],c[2],-c[0]-c[1]-c[2]]
dot=lambda a,b: sum(x*y for x,y in zip(a,b))
def system(v,n3,extra):
    psi=vecV(p); phi=vecV(f); S=vecV(s)
    Ms=[v[r]*dot(psi,S)+n3[r]*dot(phi,S) for r in range(4)]          # M s
    MTs=[psi[r]*dot(v,S)+phi[r]*dot(n3,S) for r in range(4)]         # M^T s
    Q=sp.expand(4*dot(S,S)+3*(dot(S,Ms)+dot(S,MTs))+dot(Ms,Ms))      # s^T(4 + 3(M+M^T) + M^T M)s
    eqs=[c for c in sp.Poly(Q,*s).coeffs()]
    return eqs+extra
cases=[('v=w(t0), n3=w(t3), t0!=t3',w(t0),w(t3),['u*(t0-t3)-1'],'t0,t3,u'),
       ('v=w(t0), n3=chi_3',w(t0),chi[3],[],'t0'),
       ('v=chi_3, n3=w(t3)',chi[3],w(t3),[],'t3'),
       ('n3 = v = w(t0)',w(t0),w(t0),[],'t0'),
       ('n3 = v = chi_3',chi[3],chi[3],[],'')]
for name,v,n3,extra,pv in cases:
    eqs=system(v,n3,[])
    vars_='p0,p1,p2,f0,f1,f2'+(','+pv if pv else '')
    sc='ring R=(0,I),(%s),dp; minpoly=I^2+1; option(redSB);\nideal E=%s%s;\nideal G=std(E); printf("%s: unit %%s",reduce(1,G)==0); quit;\n'%(
        vars_,','.join(str(sp.expand(e)).replace('**','^') for e in eqs),(','+','.join(extra)) if extra else '',name)
    open('supp3_deg2.sing','w').write(sc)
    print(subprocess.run(['Singular','-q','supp3_deg2.sing'],capture_output=True,text=True,timeout=300).stdout.strip(),flush=True)
# calibration: same with W of support 4-type M = sum of 3 independent isotropic rank-ones (n_j = chi_1-lines) -> expect NON-unit
v1,v2,v3=w(0),w(1),w(-1)
psi=vecV(p); phi=vecV(f); g=sp.symbols('g0:3'); gam=vecV(g); S=vecV(s)
Ms=[v1[r]*dot(psi,S)+v2[r]*dot(phi,S)+v3[r]*dot(gam,S) for r in range(4)]
MTs=[psi[r]*dot(v1,S)+phi[r]*dot(v2,S)+gam[r]*dot(v3,S) for r in range(4)]
Q=sp.expand(4*dot(S,S)+3*(dot(S,Ms)+dot(S,MTs))+dot(Ms,Ms)); eqs=sp.Poly(Q,*s).coeffs()
sc='ring R=(0,I),(p0,p1,p2,f0,f1,f2,g0,g1,g2),dp; minpoly=I^2+1;\nideal E=%s;\nideal G=std(E); printf("CALIBRATION three independent isotropic directions: unit %%s dim %%s",reduce(1,G)==0,dim(G)); quit;\n'%','.join(str(sp.expand(e)).replace('**','^') for e in eqs)
open('supp3_cal.sing','w').write(sc)
print(subprocess.run(['Singular','-q','supp3_cal.sing'],capture_output=True,text=True,timeout=300).stdout.strip())
