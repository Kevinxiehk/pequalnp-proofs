# calibration of pt2_mine.py's equations at ncol's exact example (exact over Q(i)): W_a = W_b = span(e0, chi'), chi' = (0,1,i,-1,-i),
# G = D2^perp cap V5 in the pivot chart 01. Only-d2 equations must vanish; the D3 equations must not all vanish (e = 3).
import sympy as sp, sys
src=open('pt2_mine.py').read().split("reps=[")[0].replace("P=int(sys.argv[1]) if len(sys.argv)>1 else 2147483629","P=0")
exec(src)
I=sp.I; chi=[0,1,I,-1,-I]; chi2=[c**2 for c in chi]
# G in chart (0,1): rows g0 = (1,0,x0,y0,-1-x0-y0), g1 = (0,1,x1,y1,-1-x1-y1); impose g.chi = g.chi2 = 0
x0,y0,x1,y1=sp.symbols('x0 y0 x1 y1')
g0=[1,0,x0,y0,-1-x0-y0]; g1=[0,1,x1,y1,-1-x1-y1]
dot=lambda p,q: sum(pp*qq for pp,qq in zip(p,q))
sol=sp.solve([dot(g0,chi),dot(g0,chi2),dot(g1,chi),dot(g1,chi2)],[x0,y0,x1,y1],dict=True); print('G chart solution:',sol)
T,eqs=system((0,1),(0,1),(0,1))
# T order: Wa rows (3 free each, columns 2,3,4), Wb same, G (x0,y0,x1,y1)
val={T[0]:0,T[1]:0,T[2]:0,T[3]:I,T[4]:-1,T[5]:-I, T[6]:0,T[7]:0,T[8]:0,T[9]:I,T[10]:-1,T[11]:-I}
val.update({T[12]:sol[0][x0],T[13]:sol[0][y0],T[14]:sol[0][x1],T[15]:sol[0][y1]})
vals=[sp.simplify(e.subs(val)) for e in eqs]
print('#eqs',len(eqs),' vanishing:',sum(1 for x in vals if x==0),' nonzero:',[i for i,x in enumerate(vals) if x!=0])
