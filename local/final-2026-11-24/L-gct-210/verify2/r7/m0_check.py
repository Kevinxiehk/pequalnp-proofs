# verify2 round 7: independent check of stage3's exact F4b-core example M_0 (NOTES-stage3 sec. 26 (A5')).
# (1) perm(J+m) == 120 as a polynomial identity over Z[omega] (sympy, omega^2 = -1 - omega);
# (2) invariants z, lam, dim (M_0)_r numerically; (3) dim T_1(M_0) <= 8 via a rank lower bound mod p (p = 1 mod 3) at Z[omega]-points.
import sympy as sp, itertools, numpy as np, random
W=sp.Symbol('W')  # omega
ca,cb,cc,cd,mu,ga,de=sp.symbols('ca cb cc cd mu ga de')
e1=[1,0,0,0,0]; n=[0,1,W**2,0,W]; npr=[0,1,W,0,W**2]; w=[0,-1,-1,3,-1]; p=[-1,0,0,0,0]
def row(coefs): return coefs
rows=[[ca*e1[j]+ga*n[j] for j in range(5)],[cb*e1[j]-ga*n[j] for j in range(5)],[cc*e1[j]+de*npr[j] for j in range(5)],
      [cd*e1[j]-de*npr[j] for j in range(5)],[(ca+cb+cc+cd)*p[j]+mu*w[j] for j in range(5)]]
A=[[1+rows[i][j] for j in range(5)] for i in range(5)]
per=0
for s in itertools.permutations(range(5)):
    t=1
    for i in range(5): t*=A[i][s[i]]
    per+=t
per=sp.expand(per)
red=sp.rem(sp.Poly(per,W),sp.Poly(W**2+W+1,W))
print('perm - 120 reduced mod omega^2+omega+1:',sp.expand(red.as_expr()-120))
# numeric basis
om=np.exp(2j*np.pi/3)
def num(v): return np.array([complex(sp.N(sp.sympify(x).subs(W,om))) for x in v])
E1,N,NP,Wv,P=map(num,[e1,n,npr,w,p])
basis=[]
for r in range(4):
    B=np.zeros((5,5),complex); B[r]=E1; B[4]=P; basis.append(B)
B=np.zeros((5,5),complex); B[4]=Wv; basis.append(B)
B=np.zeros((5,5),complex); B[0]=N; B[1]=-N; basis.append(B)
B=np.zeros((5,5),complex); B[2]=NP; B[3]=-NP; basis.append(B)
Mb=np.array([b.reshape(25) for b in basis]); print('dim M_0 =',np.linalg.matrix_rank(Mb))
def sub_dim(rows0):
    # dim of {m in M : rows in rows0 vanish}
    idx=[r*5+j for r in rows0 for j in range(5)]
    A=Mb[:,idx].T; return 7-np.linalg.matrix_rank(A,tol=1e-9)
names='abcde'
print('dim (M_0)_r:',[sub_dim([r]) for r in range(5)])
print('lam_rr\':',{names[r]+names[s]:sub_dim([r,s]) for r,s in itertools.combinations(range(5),2)})
print('single-row parts z_i:',[sub_dim([s for s in range(5) if s!=r]) for r in range(5)])
# (3) T_1 rank mod p
pmod=1000000000039 if False else 2147483629
assert (pmod-1)%3==0
g=2
while pow(g,(pmod-1)//3,pmod)==1: g+=1
omp=pow(g,(pmod-1)//3,pmod); assert (omp*omp+omp+1)%pmod==0
def modv(v): 
    out=[]
    for x in v:
        P_=sp.Poly(sp.sympify(x),W); out.append(sum(int(c)*pow(omp,k,pmod) for (k,),c in P_.terms())%pmod)
    return out
E1m,Nm,NPm,Wm,Pm=map(modv,[e1,n,npr,w,p])
def perm4(M):
    s=0
    for q in itertools.permutations(range(4)):
        t=1
        for i in range(4): t=t*M[i][q[i]]%pmod
        s+=t
    return s%pmod
random.seed(1)
rowsT=[]
for k in range(60):
    c=[random.randrange(-50,51) for _ in range(7)]
    mm=[[0]*5 for _ in range(5)]
    for r in range(4):
        for j in range(5): mm[r][j]+=c[r]*E1m[j]
    for j in range(5):
        mm[4][j]+=(c[0]+c[1]+c[2]+c[3])*Pm[j]+c[4]*Wm[j]
        mm[0][j]+=c[5]*Nm[j]; mm[1][j]-=c[5]*Nm[j]; mm[2][j]+=c[6]*NPm[j]; mm[3][j]-=c[6]*NPm[j]
    A_=[[(1+mm[i][j])%pmod for j in range(5)] for i in range(5)]
    cof=[]
    for i in range(5):
        for j in range(5):
            sub=[[A_[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]
            cof.append(perm4(sub))
    rowsT.append(cof)
def rank_mod(Mx):
    M=[r[:] for r in Mx]; rk=0; cols=len(M[0])
    for cidx in range(cols):
        piv=next((i for i in range(rk,len(M)) if M[i][cidx]%pmod),None)
        if piv is None: continue
        M[rk],M[piv]=M[piv],M[rk]; inv=pow(M[rk][cidx],pmod-2,pmod)
        M[rk]=[x*inv%pmod for x in M[rk]]
        for i in range(len(M)):
            if i!=rk and M[i][cidx]:
                f=M[i][cidx]; M[i]=[(x-f*y)%pmod for x,y in zip(M[i],M[rk])]
        rk+=1
    return rk
rk=rank_mod(rowsT); print('rank of 60 cofactor vectors mod p =',rk,' => dim T_1(M_0) <= ',25-rk,' over C (rank mod p <= rank in char 0)')
# numeric dim T_1 for the other direction
rowsC=[]
rng=np.random.default_rng(3)
for k in range(60):
    c=rng.normal(size=7)+1j*rng.normal(size=7); m=sum(ci*b for ci,b in zip(c,basis)); A_=np.ones((5,5))+m
    cof=[]
    for i in range(5):
        for j in range(5):
            sub=np.delete(np.delete(A_,i,0),j,1); cof.append(sum(np.prod([sub[a,q[a]] for a in range(4)]) for q in itertools.permutations(range(4))))
    rowsC.append(cof)
sv=np.linalg.svd(np.array(rowsC),compute_uv=False); print('numeric singular values (17..19):',sv[15:19]/sv[0])
