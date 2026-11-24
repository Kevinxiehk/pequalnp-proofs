import sympy as sp, itertools
a=sp.symbols('a0:4')
tau=sum(a); 
E2=[sp.expand(sum(a[p]*a[q] for p,q in itertools.combinations([k for k in range(4) if k!=i],2))) for i in range(4)]
G=sp.groebner(E2,*a,order='grevlex')
print('GB size',len(G.exprs))
for N in range(1,5):
    r=G.reduce(sp.expand((a[0]*a[1])**N))[1]
    print(N, 'rem zero' if r==0 else 'nonzero')
    if r==0: break
