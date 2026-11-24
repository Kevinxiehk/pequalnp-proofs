import sympy as sp
R=sp.Rational
z0=sp.symbols('a0:4'); z1=sp.symbols('b0:4'); d=sp.symbols('d0:4')
T,S0,S1=sp.symbols('T S0 S1')
ip=lambda x,y:sum(p*q for p,q in zip(x,y))
# hypotheses as lhs - rhs
h0=S0; h1=S1-1
hT0=S0-sum(z0); hT1=S1-sum(z1); hTd=T-sum(d)
h00=(S0**2-ip(z0,z0))/2; h11=(S1**2-ip(z1,z1))/2; h01=(S0*S1-ip(z0,z1))/2
hd0=(T*S0-ip(d,z0))/2; hd1=(T*S1-ip(d,z1))/2
u=[d[k]-T*z1[k] for k in range(4)]; f=[z1[k]-R(1,4) for k in range(4)]
def chk(name,goal,cert): print(name, sp.expand(goal-cert))
chk('hu', sum(u), -hTd + T*hT1 - T*h1)
chk('hf', sum(f), h1 - hT1)
chk('hff', ip(f,f)-R(3,4), -2*h11 + (S1+1)*h1 + R(1,2)*hT1 - R(1,2)*h1)
chk('hfg', ip(f,z0), -2*h01 + S1*h0 + R(1,4)*hT0 - R(1,4)*h0)
chk('hgg', ip(z0,z0), -2*h00 + S0*h0)
chk('huf', ip(u,f), -2*hd1 + R(1,4)*hTd + 2*T*h11 - T/4*hT1 + T*(R(1,4)-S1)*h1)
chk('hug', ip(u,z0), -2*hd0 + 2*T*h01 + T*(1-S1)*h0)
# qbar1
Y=[[sp.Symbol(f'y{i}{j}') for j in range(5)] for i in range(4)]
E=sp.Symbol('E')
col=lambda j:[Y[i][j] for i in range(4)]
uu=[(Y[i][0]+Y[i][1])/2 for i in range(4)]
rs=[sum(Y[i]) for i in range(4)]
def X2(*zs): return -2*sum(ip(zs[a],zs[b]) for a in range(4) for b in range(a+1,4))
P34=X2(uu,uu,col(3),col(4))-4*E; P24=X2(uu,uu,col(2),col(4))-4*E; P23=X2(uu,uu,col(2),col(3))-4*E
I=X2(uu,col(2),col(3),col(4))
c=sp.symbols('c0:4')
g=ip(uu,uu)-ip(rs,uu)-2*E
ex=sp.expand(g-(c[0]*P34+c[1]*P24+c[2]*P23+c[3]*I))
sol=sp.solve(sp.Poly(ex,*[s for row in Y for s in row],E).coeffs(),c,dict=True)
print('qbar1',sol)
