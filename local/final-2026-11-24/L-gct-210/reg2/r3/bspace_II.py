# Round 12, target 1, case (II): n = e3 - e4, W = {w : sum w = 0, w3 = w4}.  Linear space of B: W -> 1^perp with b skew and
# zeta = 1_S (S = {3,4}) in L_B (SK2), i.e. (Bw)_3 + (Bw)_4 = 0.  Exact (sympy rationals).
import sympy as sp, itertools
W=[sp.Matrix([1,-1,0,0,0]),sp.Matrix([1,0,-1,0,0]),sp.Matrix([2,0,0,-1,-1])]
F=[sp.Matrix([1 if c==i else (-1 if c==4 else 0) for c in range(5)]) for i in range(4)]
c=sp.symbols('c0:12'); U=[sum((c[4*i+k]*F[k] for k in range(4)),sp.zeros(5,1)) for i in range(3)]
eqs=[]
for i in range(3):
    for l in range(i,3):
        eqs.append(sp.expand((W[i].T*U[l])[0]+(W[l].T*U[i])[0]))                      # b skew
        z=sp.Matrix([0,0,0,1,1]); eqs.append(sp.expand(sum(W[i][a]*z[a]*U[l][a]+W[l][a]*z[a]*U[i][a] for a in range(5))))   # SK2 with 1_S
sol=sp.linsolve(eqs,c); sol=list(sol)[0]; free=sorted(set().union(*[s.free_symbols for s in sol]),key=str)
print('dim of B-space:',len(free),' free:',free)
Bm=sp.Matrix([[sol[4*i+k] for k in range(4)] for i in range(3)])
img=[sum((Bm[i,k]*F[k] for k in range(4)),sp.zeros(5,1)) for i in range(3)]
for i in range(3): print('B w%d ='%(i+1),list(img[i].T))
M=sp.Matrix.hstack(*img)
print('rank (generic):',M.subs({f:sp.Rational(k+2,k+3) for k,f in enumerate(free)}).rank())
