# generates Singular input for the (c3)-part-2 question: a 2-dim strongly level space N'' (rs = 0, cols 0 = 1 = u)
# with neutral columns on three pairwise distinct isotropic lines and all neutral columns active.
import sympy as sp, itertools, sys
chartP=sys.argv[1]   # 'A' : c4 = al*c2 + be*c3 ;  'B' : c3 = al*c2, c4 free
inf=sys.argv[2]      # which line is at t = oo: 'none','2','3','4'
I=sp.Symbol('I'); s,t=sp.symbols('s t'); t2,t3,t4,al,be=sp.symbols('t2 t3 t4 al be')
def vec(tt,atinf):
    a,b,c=((-1,I,0) if atinf else (1-tt**2,I*(1+tt**2),2*tt))
    return [a+b+c,a-b-c,-a+b-c,-a-b+c]
v={2:vec(t2,inf=='2'),3:vec(t3,inf=='3'),4:vec(t4,inf=='4')}
if chartP=='A': c={2:s,3:t,4:al*s+be*t}
else: c={2:s,3:al*s,4:t}
y={j:[c[j]*x for x in v[j]] for j in (2,3,4)}
u=[-(y[2][k]+y[3][k]+y[4][k])/2 for k in range(4)]
cols={0:u,1:u,2:y[2],3:y[3],4:y[4]}
ip=lambda a,b:sum(p*q for p,q in zip(a,b)); t3f=lambda a,b,cc:sum(a[i]*b[i]*cc[i] for i in range(4))
def pc(a,b,cc,d): return sum(a[i]*b[j]*cc[k]*d[l] for i,j,k,l in itertools.permutations(range(4)))
eqs=[]
for dele in (0,2,3,4):
    m=[cols[j] for j in range(5) if j!=dele]
    X2=sum(ip(m[i],m[j]) for i in range(4) for j in range(i+1,4))
    X3=sum(t3f(m[i],m[j],m[k]) for i,j,k in itertools.combinations(range(4),3))
    P=pc(*m)
    for E in (X2,X3,P):
        E=sp.expand(E.subs(I**2,-1)) if False else sp.expand(E)
        pol=sp.Poly(E,s,t)
        eqs+= [cf for cf in pol.coeffs()]
eqs=[sp.expand(e) for e in eqs]
eqs=[e for e in eqs if e!=0]
def S(e): return str(e).replace('**','^')
vars_=[x for x in (t2,t3,t4) if not (inf==str(x)[1])]+[al]+([be] if chartP=='A' else [])
dist=[]
fin=[x for x in (t2,t3,t4) if inf!=str(x)[1]]
for a_,b_ in itertools.combinations(fin,2): dist.append(a_-b_)
nz = (al*be if False else None)
print('ring r=(0,I),(%s,zz),dp; minpoly=I^2+1;' % ','.join(str(x) for x in vars_))
print('ideal J=' + ',\n'.join(S(e) for e in eqs) + ';')
dd = '*'.join(['('+S(d)+')' for d in dist]) if dist else '1'
if chartP=='A':
    print('ideal J1 = J, zz*%s*al-1; ideal G1=std(J1); "A al!=0 dim:"; dim(G1);' % dd)
    print('ideal J2 = J, al, zz*%s*be-1; ideal G2=std(J2); "A al=0,be!=0 dim:"; dim(G2);' % dd)
else:
    print('ideal J1 = J, zz*%s*al-1; ideal G1=std(J1); "B al!=0 dim:"; dim(G1);' % dd)
print('quit;')
