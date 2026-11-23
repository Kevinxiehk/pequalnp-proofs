# verify2 round 6: EXACT (mod p) proof that none of the four isotropic planes N has a one-vector extension with defect in C m.
#   Step 1: first-order system (sampled at points (k,t) of F_p^2) has rank 12 on the 16-dim A_m  => its kernel T is 4-dim and contains N.
#   Step 2: on a complement span(E1,E2) of N in T the x^2-coefficients give binary quadrics in (a,b) of rank 3 => a = b = 0.
# Sampling only weakens the system, so emptiness of the sampled system proves emptiness of the true one; the true solution set is a
# projective variety, so emptiness over F_p-bar implies emptiness in characteristic 0 (a point over Q-bar reduces to a point mod P).
import sys, itertools, random
p=int(sys.argv[1]) if len(sys.argv)>1 else 2147483629
def sqrtm(a):
    a%=p
    if a==0: return 0
    assert pow(a,(p-1)//2,p)==1,'non-residue'
    if p%4==3: return pow(a,(p+1)//4,p)
    q,s=p-1,0
    while q%2==0: q//=2; s+=1
    z=2
    while pow(z,(p-1)//2,p)!=p-1: z+=1
    c=pow(z,q,p); r=pow(a,(q+1)//2,p); t=pow(a,q,p); mm=s
    while t!=1:
        i=0; tt=t
        while tt!=1: tt=tt*tt%p; i+=1
        b=pow(c,1<<(mm-i-1),p); r=r*b%p; c=b*b%p; t=t*c%p; mm=i
    return r
inv=lambda a: pow(a%p,p-2,p)
I=sqrtm(-1); s3=sqrtm(3); w=(-1+I*s3)*inv(2)%p; assert (w*w+w+1)%p==0 and I*I%p==p-1
one=[1]*4; chi1=[1,I,p-1,(p-I)%p]; chi2=[1,p-1,1,p-1]; m=[1,w,w*w%p,0,0]; mbar=[1,w*w%p,w,0,0]
P3=list(itertools.permutations(range(3)))
def perm3(U,rows,cols): return sum(U[rows[0]][cols[q[0]]]*U[rows[1]][cols[q[1]]]*U[rows[2]][cols[q[2]]] for q in P3)%p
def perm2(U,rows,cols): return (U[rows[0]][cols[0]]*U[rows[1]][cols[1]]+U[rows[0]][cols[1]]*U[rows[1]][cols[0]])%p
Wm=[[0,0,0,1,0],[0,0,0,0,1],[w,p-1,0,0,0],[w*w%p,0,p-1,0,0]]
def EBn(n):                       # basis of A_m: n = 5r+c (r = 0,1,2): E[r][c] = 1, E[3][c] = -1;  n = 15: row 3 = m
    E=[[0]*5 for _ in range(4)]
    if n<15: r,c=divmod(n,5); E[r][c]=1; E[3][c]=p-1
    else: E[3]=m[:]
    return E
EB=[EBn(n) for n in range(16)]
def coords(M):                    # coordinates of a matrix of A_m in the basis EB
    lam=None
    for c in range(5):
        if m[c]: lam=sum(M[r][c] for r in range(4))*inv(m[c])%p; break
    v=[M[r][c]%p for r in range(3) for c in range(5)]+[lam]
    # check
    for r in range(4):
        for c in range(5): assert sum(v[n]*EB[n][r][c] for n in range(16))%p==M[r][c]%p
    return v
def rref(rows,ncol):
    rows=[r[:] for r in rows]; piv=[]; rk=0
    for c in range(ncol):
        pr=next((i for i in range(rk,len(rows)) if rows[i][c]%p),None)
        if pr is None: continue
        rows[rk],rows[pr]=rows[pr],rows[rk]; iv=inv(rows[rk][c]); rows[rk]=[x*iv%p for x in rows[rk]]
        for i in range(len(rows)):
            if i!=rk and rows[i][c]%p:
                f=rows[i][c]; rows[i]=[(x-f*y)%p for x,y in zip(rows[i],rows[rk])]
        piv.append(c); rk+=1
        if rk==len(rows): break
    return rk,piv,rows[:rk]
def kernel(rows,ncol):
    rk,piv,R=rref(rows,ncol); free=[c for c in range(ncol) if c not in piv]; K=[]
    for f in free:
        v=[0]*ncol; v[f]=1
        for row,c in zip(R,piv): v[c]=(-row[f])%p
        K.append(v)
    return rk,K
def first_order_rows(Y0):
    U=[[(1+Y0[r][c])%p for c in range(5)] for r in range(4)]
    G=[[[0]*5 for _ in range(4)] for _ in range(5)]
    for j in range(5):
        for r in range(4):
            rows=[x for x in range(4) if x!=r]
            for c in range(5):
                if c!=j: G[j][r][c]=perm3(U,rows,[x for x in range(5) if x not in (j,c)])
    D=[[sum(G[j][r][c]*EB[n][r][c] for r in range(4) for c in range(5))%p for n in range(16)] for j in range(5)]
    return [[sum(Wm[i][j]*D[j][n] for j in range(5))%p for n in range(16)] for i in range(4)]
def hess(Y0,E,Ep):
    U=[[(1+Y0[r][c])%p for c in range(5)] for r in range(4)]; out=[]
    for j in range(5):
        tot=0
        for r in range(4):
            for rp in range(4):
                if rp==r: continue
                rows=[x for x in range(4) if x not in (r,rp)]
                for c in range(5):
                    if c==j or not E[r][c]: continue
                    for cp in range(5):
                        if cp in (j,c) or not Ep[rp][cp]: continue
                        tot+=E[r][c]*Ep[rp][cp]*perm2(U,rows,[x for x in range(5) if x not in (j,c,cp)])
        out.append(tot%p)
    return [sum(Wm[i][j]*out[j] for j in range(5))%p for i in range(4)]
rnd=random.Random(7); ok_all=True
print('prime',p)
for case,(sb,sx) in (('A1',(1,1)),('A2',(1,-1)),('A3',(-1,1)),('A4',(-1,-1))):
    beta=sb*s3*inv(4)%p; xi=sx*sqrtm(-3*inv(32*beta))%p; assert xi*xi%p==(-3*inv(32*beta))%p
    h0=[(inv(4)+beta*c)%p for c in chi2]
    Z=[[(h0[r]*m[c]+chi1[r]*[0,xi,(p-xi)%p,0,0][c])%p for c in range(5)] for r in range(4)]
    Zs=[[chi1[r]*mbar[c]%p for c in range(5)] for r in range(4)]
    pts=[(rnd.randrange(p),rnd.randrange(p)) for _ in range(14)]
    Y0s=[[[(k*Z[r][c]+t*Zs[r][c])%p for c in range(5)] for r in range(4)] for k,t in pts]
    A=[row for Y0 in Y0s for row in first_order_rows(Y0)]
    rk,K=kernel(A,16)
    zc,zsc=coords(Z),coords(Zs)
    inK=all(sum(a*b for a,b in zip(row,v))%p==0 for row in A for v in (zc,zsc))
    # complement of N in the kernel
    r4,_,_=rref([zc,zsc]+K,16); comp=[]
    for v in K:
        if rref([zc,zsc]+comp+[v],16)[0]==2+len(comp)+1: comp.append(v)
    Es=[[[sum(v[n]*EB[n][r][c] for n in range(16))%p for c in range(5)] for r in range(4)] for v in comp]
    msg='case %s: first-order rank %d (kernel dim %d), N inside kernel: %s, kernel = N + %d directions'%(case,rk,len(K),inK,len(comp))
    if len(comp)==2:
        M2=[]
        for Y0 in Y0s:
            h11=hess(Y0,Es[0],Es[0]); h12=hess(Y0,Es[0],Es[1]); h21=hess(Y0,Es[1],Es[0]); h22=hess(Y0,Es[1],Es[1])
            for i in range(4): M2.append([h11[i],(h12[i]+h21[i])%p,h22[i]])
        r2=rref(M2,3)[0]; msg+='; rank of the binary quadrics (x^2-coefficients on the complement) = %d'%r2
        ok=(rk==12 and inK and r2==3)
    else: ok=False
    print(msg,'->','NO EXTENSION (proved)' if ok else 'not decided by this method'); ok_all&=ok
print('all four cases proved:',ok_all)
