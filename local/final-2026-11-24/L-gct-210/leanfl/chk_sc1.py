import sympy as sp, itertools
Y=sp.Matrix(4,5,lambda i,j: sp.Symbol('y%d%d'%(i,j))); x=sp.Matrix(sp.symbols('x0:4'))
tau=lambda v: sum(v); ip=lambda a,b: sum(a[i]*b[i] for i in range(4))
def qA2(W,b):
    cols=[W[:,j] for j in range(5) if j!=b]
    return 2*sum(tau(cols[i])*tau(cols[j]) for i,j in itertools.combinations(range(4),2)) - 2*sum(ip(cols[i],cols[j]) for i,j in itertools.combinations(range(4),2))
ok=True
for n in range(5):
    E=sp.zeros(4,5); E[:,n]=x
    s=sp.Matrix([sum(Y[i,j] for j in range(5)) for i in range(4)])
    S=sum(tau(Y[:,j]) for j in range(5))
    for b in range(5):
        lhs=qA2(Y+E,b)-qA2(Y-E,b)
        rhs=0 if b==n else 4*tau(x)*(S-tau(Y[:,b])-tau(Y[:,n]))+4*(ip(x,Y[:,b])+ip(x,Y[:,n])-ip(x,s))
        if sp.expand(lhs-rhs)!=0: ok=False; print('fail',n,b)
print('polar ok' if ok else 'polar FAIL')
