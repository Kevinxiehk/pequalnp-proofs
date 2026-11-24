QI=True
ts=sp.Symbol('t'); PAR=[ts]; I=sp.I
xq=3*I*(1+2*ts**2); yq=2*ts**2-4*ts-1; zq=1-2*ts-2*ts**2
b1=[1,-1,0,0]; b2=[1,1,-2,0]; b3=[1,1,1,-3]
u=[sp.expand(xq*b1[k]+yq*b2[k]+zq*b3[k]) for k in range(4)]
mm=[sp.Integer(0)]+u
Zb=[]
for k in (2,3,4):
    zz=[sp.Integer(0)]*5; zz[0]=u[0]-u[k-1]; zz[1]=u[k-1]; zz[k]=-u[0]; Zb.append([sp.expand(v) for v in zz])
def mat(rows):
    M=sp.zeros(5,5)
    for (i_,j_),v in rows.items(): M[i_,j_]=v
    return M
BS=[mat({(1,j_):mm[j_] for j_ in range(5)}), mat({(1,0):1,(2,0):-1})]+[mat({(4,j_):zz[j_] for j_ in range(5)}) for zz in Zb]
