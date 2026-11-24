# Symmetric cut on the slice a2 = 0 (n = (a1, 0, a3, a4)) with the residual swap of columns 3,4 [NOTES-stage2 R16-5].
import itertools, sympy as sp
a1,a3,a4=sp.symbols('a1 a3 a4'); V=[a1,a3,a4]
def sl(e): return e
H=[a1+2*a3-6*a4]; A=[a1]; D=[a1+a3-4*a4]
pts=[(1,0,1),(1,1,1)]     # (a1,a3,a4) of the 0/1 points with a2 = 0: (1,0,0),(1,0,1)
def ptlin(p): return [V[i]*p[j]-V[j]*p[i] for i in range(3) for j in range(i+1,3)]
pieces={'H':H,'A':A,'D':D,'P0':ptlin(pts[0]),'P1':ptlin(pts[1])}
sw={a1:a1,a3:a4,a4:a3}
res=set()
for c1,c2 in itertools.product(pieces,repeat=2):
    eqs=pieces[c1]+[e.xreplace(sw) for e in pieces[c2]]
    M=sp.Matrix([[sp.Poly(e,*V).coeff_monomial(v) for v in V] for e in eqs]); r=M.rank()
    if r<3: res.add((2-r,str(sorted([list(v) for v in sp.Matrix.hstack(*M.nullspace()).T.rref()[0].tolist()]))))
for d,v in sorted(res): print('  dim',d,': n = (a1,0,a3,a4) in span',v)
