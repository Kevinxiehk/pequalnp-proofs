import sympy as sp, itertools
X=[sp.symbols(f'{c}0:4') for c in 'xyzw']
tau=lambda v:sum(v)
ip=lambda a,b:sum(p*q for p,q in zip(a,b))
t3=lambda a,b,c:sum(a[i]*b[i]*c[i] for i in range(4))
t4=lambda a,b,c,d:sum(a[i]*b[i]*c[i]*d[i] for i in range(4))
br=lambda a,b,c,d:-6*t4(a,b,c,d)+ip(a,b)*ip(c,d)+ip(a,c)*ip(b,d)+ip(a,d)*ip(b,c)
def pc(a,b,c,d):
    return sum(a[i]*b[j]*c[k]*d[l] for i,j,k,l in itertools.permutations(range(4)))
x,y,z,w=X
rhs=(tau(x)*tau(y)*tau(z)*tau(w)-(tau(x)*tau(y)*ip(z,w)+tau(x)*tau(z)*ip(y,w)+tau(x)*tau(w)*ip(y,z)+tau(y)*tau(z)*ip(x,w)+tau(y)*tau(w)*ip(x,z)+tau(z)*tau(w)*ip(x,y))
     +2*(tau(x)*t3(y,z,w)+tau(y)*t3(x,z,w)+tau(z)*t3(x,y,w)+tau(w)*t3(x,y,z))+br(x,y,z,w))
print('pc_full',sp.expand(pc(x,y,z,w)-rhs))
# nbar identities with tau(a)=tau(b)=tau(c)=0: impose by substituting a3=-a0-a1-a2 etc
a,b,c=[list(sp.symbols(f'{s}0:3'))for s in 'abc']
for v in (a,b,c): v.append(-v[0]-v[1]-v[2])
u=[-(a[k]+b[k]+c[k])/2 for k in range(4)]
def X3c(z1,z2,z3,z4):
    T=tau
    return ((T(z1)*T(z2)*T(z3)-T(z1)*ip(z2,z3)-T(z2)*ip(z1,z3)-T(z3)*ip(z1,z2)+2*t3(z1,z2,z3))
     +(T(z1)*T(z2)*T(z4)-T(z1)*ip(z2,z4)-T(z2)*ip(z1,z4)-T(z4)*ip(z1,z2)+2*t3(z1,z2,z4))
     +(T(z1)*T(z3)*T(z4)-T(z1)*ip(z3,z4)-T(z3)*ip(z1,z4)-T(z4)*ip(z1,z3)+2*t3(z1,z3,z4))
     +(T(z2)*T(z3)*T(z4)-T(z2)*ip(z3,z4)-T(z3)*ip(z2,z4)-T(z4)*ip(z2,z3)+2*t3(z2,z3,z4)))
cub=-(t3(a,a,b)+t3(a,a,c)+t3(b,b,a)+t3(b,b,c)+t3(c,c,a)+t3(c,c,b)+t3(a,b,c))
print('nbar_cubic',sp.expand(X3c(u,a,b,c)-cub))
quart=3*(t4(a,a,b,c)+t4(b,b,a,c)+t4(c,c,a,b))-(ip(a,b)*ip(a,c)+ip(b,a)*ip(b,c)+ip(c,a)*ip(c,b))
# br(u,a,b,c) - quart should be combination of ip(a,a), ip(b,b), ip(c,c)
d=sp.expand(br(u,a,b,c)-quart)
gaa,gbb,gcc=ip(a,a),ip(b,b),ip(c,c)
cand=-(gaa*ip(b,c)+gbb*ip(a,c)+gcc*ip(a,b))/2
print('nbar_quartic (br form) residue', sp.expand(d-cand))
# exact (no tau substitution) check of the br identity
a,b,c=[list(sp.symbols(f'{s}0:4')) for s in 'abc']
u=[-(a[k]+b[k]+c[k])/2 for k in range(4)]
quart=3*(t4(a,a,b,c)+t4(b,b,a,c)+t4(c,c,a,b))-(ip(a,b)*ip(a,c)+ip(b,a)*ip(b,c)+ip(c,a)*ip(c,b))
cand=-(ip(a,a)*ip(b,c)+ip(b,b)*ip(a,c)+ip(c,c)*ip(a,b))/2
print('br exact', sp.expand(br(u,a,b,c)-quart-cand))
cub=-(t3(a,a,b)+t3(a,a,c)+t3(b,b,a)+t3(b,b,c)+t3(c,c,a)+t3(c,c,b)+t3(a,b,c))
print('2 sum t3 exact', sp.expand(2*(t3(u,a,b)+t3(u,a,c)+t3(u,b,c)+t3(a,b,c))-cub))
