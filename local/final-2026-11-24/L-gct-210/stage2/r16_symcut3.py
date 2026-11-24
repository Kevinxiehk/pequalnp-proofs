# Symmetric cut inside A = {a1 = 0}: n = (0, a2, a3, a4), S_3 on (a2,a3,a4); pieces from the a1 = 0 family analysis [NOTES-stage2 R16-5].
import itertools, sympy as sp
b=sp.symbols('a2 a3 a4'); V=list(b)
def ptlin(p): return [V[i]*p[j]-V[j]*p[i] for i in range(3) for j in range(i+1,3)]
pieces={'H':[b[0]+2*b[1]-6*b[2]],'E1':[b[0]],'E2':[b[0]+b[1]-4*b[2]],'J':[b[0]+b[1]+b[2]],'P0':ptlin((1,0,1)),'P1':ptlin((1,1,1))}
perms=list(itertools.permutations(range(3))); res=set()
def act(eqs,s): return [e.xreplace({V[i]:V[s[i]] for i in range(3)}) for e in eqs]
def dfs(k,eqs):
    if eqs:
        M=sp.Matrix([[sp.Poly(e,*V).coeff_monomial(v) for v in V] for e in eqs]); r=M.rank()
        if r==3: return
        if k==len(perms): res.add((2-r,str(sorted([list(v) for v in sp.Matrix.hstack(*M.nullspace()).T.rref()[0].tolist()])))); return
    for c in pieces: dfs(k+1,eqs+act(pieces[c],perms[k]))
dfs(0,[])
for d,v in sorted(res): print('  dim',d,': (a2,a3,a4) in span',v)
