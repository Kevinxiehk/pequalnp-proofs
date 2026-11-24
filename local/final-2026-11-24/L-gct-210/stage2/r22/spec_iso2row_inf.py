QI=True
ts=None; PAR=[]; I=sp.I
b1=[1,-1,0,0]; b2=[1,1,-2,0]; b3=[1,1,1,-3]
u=[I,-I,sp.Integer(-1),sp.Integer(1)]   # t = infinity: u(inf) = (6i,-6i,-6,6) ~ (i,-i,-1,1)
mm=[sp.Integer(0)]+u
Zb=[]
for k in (2,3,4):
    zz=[sp.Integer(0)]*5; zz[0]=u[0]-u[k-1]; zz[1]=u[k-1]; zz[k]=-u[0]; Zb.append([sp.expand(v) for v in zz])
def mat(rows):
    M=sp.zeros(5,5)
    for (i_,j_),v in rows.items(): M[i_,j_]=v
    return M
BS=[mat({(1,j_):mm[j_] for j_ in range(5)}), mat({(1,0):1,(2,0):-1})]+[mat({(4,j_):zz[j_] for j_ in range(5)}) for zz in Zb]
