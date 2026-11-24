# verify2 r17: Lemma RS (iv) -- is sigma_3(Y minus column k) proportional to
#   E_k = -(3/2) t(r,r,r) + (3/2) t(r,r,x_k) - t(r,x_k,x_k) + t(x_k,x_k,x_k) + (1/2) sum_i t(x_i,x_i,r-x_k),  x_i = r - 2 y_i, r = sum_i y_i,
# for column-centred 4x5 Y (columns y_i in 1^perp of C^4), t(a,b,c) = sum_rows a b c?  Test as a polynomial identity (no degree-2 conditions), and
# modulo the degree-2 conditions <y_k, r - y_k> = 0 if needed.
import sympy as sp, itertools
Yv=sp.symbols('y0:15'); cols=[]
k=0
for i in range(5):
    c=[Yv[3*i],Yv[3*i+1],Yv[3*i+2]]; c.append(-sum(c)); cols.append(sp.Matrix(c))
r=sum(cols,sp.zeros(4,1)); x=[r-2*c for c in cols]
t=lambda a,b,c: sum(a[j]*b[j]*c[j] for j in range(4))
def sig3_del(k):
    M=sp.Matrix.hstack(*[cols[j] for j in range(5) if j!=k])  # 4x4
    return sp.expand(sum(M[i1,j1]*M[i2,j2]*M[i3,j3] for (i1,i2,i3) in itertools.combinations(range(4),3) for (j1,j2,j3) in itertools.permutations(range(4),3)))
E=lambda k: sp.expand(-sp.Rational(3,2)*t(r,r,r)+sp.Rational(3,2)*t(r,r,x[k])-t(r,x[k],x[k])+t(x[k],x[k],x[k])+sp.Rational(1,2)*sum(t(x[i],x[i],r-x[k]) for i in range(5)))
s3=sig3_del(0); e0=E(0)
import random
vals=[{v:random.randint(-9,9) for v in Yv} for _ in range(4)]
print('ratios sigma3/E at random points (no deg-2 conditions):',[ (s3.subs(v)/e0.subs(v)) if e0.subs(v)!=0 else None for v in vals])
for lam in (1,-1,sp.Rational(1,2),-sp.Rational(1,2),2,-2,sp.Rational(1,4),-sp.Rational(1,4),sp.Rational(1,8),-sp.Rational(1,8)):
    if sp.expand(s3-lam*e0)==0: print('IDENTITY: sigma_3(Y_-0) =',lam,'* E_0  (pure polynomial identity)')
# modulo degree-2 conditions
deg2=[sp.expand(sum(cols[j][a]*(r[a]-cols[j][a]) for a in range(4))) for j in range(5)]
G=sp.groebner(deg2,*Yv,order='grevlex')
for lam in (1,-1,sp.Rational(1,2),-sp.Rational(1,2),2,-2,sp.Rational(1,4),-sp.Rational(1,4),sp.Rational(3,2),-sp.Rational(3,2),sp.Rational(1,3),-sp.Rational(1,3)):
    if G.reduce(sp.expand(s3-lam*e0))[1]==0: print('MODULO deg-2: sigma_3(Y_-0) =',lam,'* E_0')
print('sum_k E_k minus (sum_k t(x_k,x_k,x_k) - 3 t(r,r,r)):',sp.factor(sp.expand(sum(E(kk) for kk in range(5))-(sum(t(x[kk],x[kk],x[kk]) for kk in range(5))-3*t(r,r,r)))))
