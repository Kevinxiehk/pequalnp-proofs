import sympy as sp, itertools
Yv=sp.symbols('y0:15'); cols=[]
for i in range(5):
    c=[Yv[3*i],Yv[3*i+1],Yv[3*i+2]]; c.append(-sum(c)); cols.append(sp.Matrix(c))
r=sum(cols,sp.zeros(4,1)); x=[r-2*c for c in cols]
W=[sp.Matrix([1,1,-1,-1])/2,sp.Matrix([1,-1,1,-1])/2,sp.Matrix([1,-1,-1,1])/2]
wc=lambda a:[(a.T*w)[0] for w in W]
t=lambda a,b,c: sum(p*q*u for p,q,u in zip(wc(a),wc(b),wc(c)))
def sig3_del(k):
    M=sp.Matrix.hstack(*[cols[j] for j in range(5) if j!=k])
    return sp.expand(sum(M[i1,j1]*M[i2,j2]*M[i3,j3] for (i1,i2,i3) in itertools.combinations(range(4),3) for (j1,j2,j3) in itertools.permutations(range(4),3)))
E=lambda k: sp.expand(-sp.Rational(3,2)*t(r,r,r)+sp.Rational(3,2)*t(r,r,x[k])-t(r,x[k],x[k])+t(x[k],x[k],x[k])+sp.Rational(1,2)*sum(t(x[i],x[i],r-x[k]) for i in range(5)))
deg2=[sp.expand(sum(cols[j][a]*(r[a]-cols[j][a]) for a in range(4))) for j in range(5)]
f=lambda e: str(sp.expand(8*e))  # clear the 1/2's
out=['ring R=0,(%s),dp;'%','.join(map(str,Yv)),'ideal D=%s; D=std(D);'%','.join(map(str,deg2)),
 'poly s3=%s; poly e0=%s;'%(f(sig3_del(0)),f(E(0))),
 'poly a=reduce(s3,D); poly b=reduce(e0,D); "NF(sigma3) zero:",a==0," NF(E0) zero:",b==0;',
 'matrix m[1][2]=a,b; ideal q=a,b; "deg NF:",deg(a),deg(b);',
 '// test proportionality: a*lc(b)-b*lc(a)',
 'poly d=a*leadcoef(b)-b*leadcoef(a); "proportional mod deg-2:",d==0; if(d==0){"ratio sigma3/E0 =",leadcoef(a)/leadcoef(b);}',
 'quit;']
open('rs_iv_walsh.sing','w').write('\n'.join(out)+'\n')
