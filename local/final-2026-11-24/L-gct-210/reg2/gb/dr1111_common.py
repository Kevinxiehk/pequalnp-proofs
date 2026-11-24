# shared part of gen_dr211d.py / cert_dr211.py (exec'd; expects comp in {'g','d'}).  Builds the Family F, the vectors A (a), Bv, Cv,
# and charts() -> list of (jc, ja, base equations, pivot-zero list).
def det3(M):
    return add(add(mul(M[0][0],add(mul(M[1][1],M[2][2]),mul(M[1][2],M[2][1]),-1)),
                   mul(M[0][1],add(mul(M[1][0],M[2][2]),mul(M[1][2],M[2][0]),-1)),-1),
               mul(M[0][2],add(mul(M[1][0],M[2][1]),mul(M[1][1],M[2][0]),-1)))
def cross4(R,b,c):
    one=R.const(1); A_=[[one]*4,b,c]; out=[]
    for j in range(4):
        cols=[k for k in range(4) if k!=j]; out.append(scal(det3([[A_[i][k] for k in cols] for i in range(3)]),(-1)**j))
    return out
def vec4(R,V,p):
    v=[V(p+'1'),V(p+'2'),V(p+'3')]; v.append(scal(add(add(v[0],v[1]),v[2]),-1)); return v
store={}
def basis(R,V):
    # (1,1,1,1|2) case A: row 0 = g = (1,1,1,1,-4); rows 1,2,3 = (b,0), (c,0), (a,0); V = {x_0 = 0, sum = 0} in column 4
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    b=vec4(R,V,'b')
    cc=vec4(R,V,'c') if comp=='g' else b
    a=cross4(R,b,cc if comp=='g' else [mul(x,x) for x in b])
    store['a']=a; store['b']=b; store['c']=cc
    B0=Z(); B0[0]=[c(1),c(1),c(1),c(1),c(-4)]
    B1=Z(); B2=Z(); B3=Z()
    for j in range(4): B1[1][j]=b[j]; B2[2][j]=cc[j]; B3[3][j]=a[j]
    B4=Z(); B4[1][4]=c(1); B4[2][4]=c(-1)
    B5=Z(); B5[2][4]=c(1); B5[3][4]=c(-1)
    return [B0,B1,B2,B3,B4,B5]
params=['b1','b2','b3']+(['c1','c2','c3'] if comp=='g' else [])+['z']
F=Family(params,basis,6); W=F.W
strip=lambda q:{k[6:]:v for k,v in q.items()}
A=[strip(q) for q in store['a']]; Bv=[strip(q) for q in store['b']]; Cv=[strip(q) for q in store['c']]
extra_rel=[]
if comp=='d':
    bb={}
    for q in Bv: bb=add(bb,mul(q,q))
    extra_rel=[bb]
def charts():
    out=[]
    for jc in ([1,2] if comp=='g' else [None]):
        for ja in range(4):
            base=F.level+extra_rel+[F.eq('b1',1), add(mul(W('z'),A[ja]),F.c(-1))]
            if jc is not None: base=base+[add(Cv[jc-1],F.c(-1))]
            jcc=jc if jc is not None else 1
            zero=['x04','x10','x2%d'%(jcc-1),'x3%d'%ja,'x14','x24','x34']
            out.append((jc,ja,base,zero))
    return out
