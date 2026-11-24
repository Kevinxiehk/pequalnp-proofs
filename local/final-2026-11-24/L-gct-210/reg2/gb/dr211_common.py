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
    c=R.const; Z=lambda: [[{} for _ in range(5)] for _ in range(4)]
    b=vec4(R,V,'b')
    cc=vec4(R,V,'c') if comp=='g' else b
    a=cross4(R,b,cc if comp=='g' else [mul(x,x) for x in b])
    store['a']=a; store['b']=b; store['c']=cc
    B1=Z(); B1[0][0]=c(4)
    for j in range(1,5): B1[0][j]=c(-1)
    B2=Z(); B3=Z(); B4=Z()
    for j in range(4): B2[0][1+j]=a[j]; B3[1][1+j]=b[j]; B4[2][1+j]=cc[j]
    B5=Z(); B5[1][0]=c(1); B5[2][0]=c(-1)
    B6=Z(); B6[2][0]=c(1); B6[3][0]=c(-1)
    return [B1,B2,B3,B4,B5,B6]
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
            zero=['x00','x10','x20','x34','x0%d'%(ja+1),'x11','x2%d'%jcc]
            if comp=='d': zero=['x00','x10','x20','x34','x0%d'%(ja+1),'x11','x21']
            out.append((jc,ja,base,zero))
    return out
