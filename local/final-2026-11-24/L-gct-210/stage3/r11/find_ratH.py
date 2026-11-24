# rational points of H: y = w3 (columns 1..4) integer with sum 0, la rational root of sum_j y_j prod_{k != j}(y_k - la) = 0, x_j = y_j/(y_j - la)
import itertools, sympy as sp
la=sp.symbols('la'); found=[]
for y in itertools.product(range(-4,5),repeat=3):
    yy=list(y)+[-sum(y)]
    if len(set(yy))<4 or 0 in yy: continue
    f=sp.expand(sum(yy[j]*sp.prod([yy[k]-la for k in range(4) if k!=j]) for j in range(4)))
    for r in sp.Poly(f,la).ground_roots():
        if r!=0 and all(yy[j]!=r for j in range(4)):
            x=[sp.Rational(yy[j])/(yy[j]-r) for j in range(4)]
            if sum(x)==0 and len(set(x))>2: found.append((yy,r,x))
    if len(found)>=6: break
for yy,r,x in found: print('w3 =',[0]+yy,' la =',r,' w2 =',[0]+[str(t) for t in x])
