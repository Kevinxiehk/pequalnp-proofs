# family (A) check without parametrizing W: diag(x) - k I = 1 al^T + al 1^T + x be^T + be x^T (as symmetric matrices), x in V.
import sympy as sp
x1,x2,x3,k=sp.symbols('x1 x2 x3 k'); al=sp.symbols('al1:5'); be=sp.symbols('be1:5')
X=[x1,x2,x3,-x1-x2-x3]
eqs=[]
for i in range(4):
    for j in range(i,4):
        lhs=(X[i]-k if i==j else 0)
        rhs=al[i]+al[j]+X[i]*be[j]+X[j]*be[i]
        eqs.append(lhs-rhs)
eqs.append(be[3])  # gauge (al,be) -> (al+c x, be-c 1)
for chart in ([x1-1],[x1,x2-1],[x1,x2,x3-1]):
    G=sp.groebner(eqs+chart,*al,*be,k,x1,x2,x3,order='lex')
    sols=sp.solve(list(G.exprs),[*al,*be,k,x1,x2,x3],dict=True)
    xs=set()
    for s in sols:
        v=tuple(sp.nsimplify(e.subs(s)) for e in X)
        if all(e.free_symbols==set() for e in v): xs.add(v)
        else: xs.add(('FAMILY',)+v)
    print(chart, sorted(xs,key=str))
