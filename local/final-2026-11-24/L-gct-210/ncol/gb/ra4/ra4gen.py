# (PROD), stratum r_a = 4 (pi_a(S) a hyperplane n^perp, S_b = 0): S = {(a, beta) : a in n^perp, (I-J) beta = Phi a + (k.a) n},
# Phi 5x5 skew with last row/column 0, k with k_4 = 0, chart n_4 = 1 (S5-symmetry: WLOG n_4 != 0).  Isotropy is built in; equations:
# coefficients of e_3(a) + e_3(beta) in t (20 equations, 14 unknowns).  usage: python3 -I ra4gen.py P OUT.ms
import sympy as sp, itertools, sys
P=int(sys.argv[1]); out=sys.argv[2]
t=sp.symbols('t0:4'); n=list(sp.symbols('n0:4'))+[1]
ph=sp.symbols('p0:6'); k=list(sp.symbols('k0:4'))+[0]
Phi=sp.zeros(5,5); idx=0
for i in range(4):
    for j in range(i+1,4):
        Phi[i,j]=ph[idx]; Phi[j,i]=-ph[idx]; idx+=1
a=list(t)+[-sum(n[j]*t[j] for j in range(4))]
ka=sum(k[j]*a[j] for j in range(5))
g=[sp.expand(sum(Phi[i,j]*a[j] for j in range(5))+ka*n[i]) for i in range(5)]
G=sum(g); beta=[sp.expand(g[i]-G/4) for i in range(5)]
def e3(v): return sum(v[i]*v[j]*v[l] for i,j,l in itertools.combinations(range(5),3))
F=sp.expand(e3(a)+e3(beta))
unk=list(n[:4])+list(ph)+list(k[:4])
coeffs=sp.Poly(F,*t).coeffs()
lines=[]
for c in coeffs:
    pol=sp.Poly(sp.expand(c),*unk); terms=[]
    for mon,cf in pol.terms():
        cf=sp.Rational(cf); v=(int(cf.p)%P)*pow(int(cf.q)%P,P-2,P)%P
        if v==0: continue
        mono='*'.join(('%s^%d'%(u,e) if e>1 else str(u)) for u,e in zip(unk,mon) if e)
        terms.append(str(v)+('*'+mono if mono else ''))
    if terms: lines.append('+'.join(terms))
open(out,'w').write(','.join(str(u) for u in unk)+'\n%d\n'%P+',\n'.join(lines)+'\n')
print('wrote',len(lines),'equations')
