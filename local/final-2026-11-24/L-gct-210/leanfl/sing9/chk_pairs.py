import sympy as sp
I=sp.I
def vec(t):
    if t=='inf': a,b,c=-1,I,0
    else: a,b,c=1-t**2,I*(1+t**2),2*t
    return [sp.expand(x) for x in (a+b+c,a-b-c,-a+b-c,-a-b+c)]
x=sp.symbols('x')
pairs=[(0,'inf'),(1,-1),(I,-I)]
for q in [x**2+(I-1)*x+I,x**2+(-I-1)*x-I,x**2+(I+1)*x-I,x**2+(-I+1)*x+I]:
    r=sp.solve(q,x); pairs.append(tuple(r))
for (t,u) in pairs:
    v,w=vec(t),vec(u)
    f1=sp.simplify(sum(v[k]*w[k]**2 for k in range(4))); f2=sp.simplify(sum(v[k]**2*w[k] for k in range(4)))
    t3v=sp.simplify(sum(c**3 for c in v)); zer=[k for k in range(4) if sp.simplify(v[k])==0]; zerw=[k for k in range(4) if sp.simplify(w[k])==0]
    print('pair',t,u,'f1',f1,'f2',f2,'tau(v^3)',t3v,'zero coords v',zer,'w',zerw)
