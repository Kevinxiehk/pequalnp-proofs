import sympy as sp
Y=[[sp.Symbol(f'y{i}{j}') for j in range(5)] for i in range(4)]
E=sp.Symbol('E')
col=lambda j:[Y[i][j] for i in range(4)]
u=[(Y[i][0]+Y[i][1])/2 for i in range(4)]
rs=[sum(Y[i]) for i in range(4)]
ip=lambda x,y:sum(a*b for a,b in zip(x,y))
def X2(z1,z2,z3,z4):
    zs=[z1,z2,z3,z4]
    return -2*sum(ip(zs[a],zs[b]) for a in range(4) for b in range(a+1,4))
a34=X2(u,u,col(3),col(4))-4*E
a24=X2(u,u,col(2),col(4))-4*E
a23=X2(u,u,col(2),col(3))-4*E
bI=X2(u,col(2),col(3),col(4))
R=sp.Rational
for j,c in [(2,(R(-1,3),R(1,6),R(1,6))),(3,(R(1,6),R(-1,3),R(1,6))),(4,(R(1,6),R(1,6),R(-1,3)))]:
    g=ip(col(j),col(j))-ip(rs,col(j))
    print(j,sp.expand(g-(c[0]*a34+c[1]*a24+c[2]*a23+R(1,3)*bI)))
