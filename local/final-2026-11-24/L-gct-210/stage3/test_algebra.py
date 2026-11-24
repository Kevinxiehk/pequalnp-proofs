import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
from s3lib import *
rng=np.random.default_rng(2)
SUB={k:list(itertools.combinations(R5,k)) for k in range(6)}
IDX={k:{S:i for i,S in enumerate(SUB[k])} for k in range(6)}
def mul(u,ku,v,kv):
    """product in A = C[y]/(y_j^2): u in A_ku, v in A_kv (coefficient vectors)"""
    out=np.zeros(len(SUB[ku+kv]),complex)
    for S,i in IDX[ku].items():
        if u[i]==0: continue
        for T,j in IDX[kv].items():
            if v[j]==0 or set(S)&set(T): continue
            out[IDX[ku+kv][tuple(sorted(S+T))]]+=u[i]*v[j]
    return out
lin=lambda v: np.asarray(v,complex)
def prodrows(rows):
    w=lin(rows[0]); k=1
    for r in rows[1:]: w=mul(w,k,lin(r),1); k+=1
    return w
# (0) coefficients of V_1..V_k = k x k subpermanents
M=rng.normal(size=(3,5)); w=prodrows(list(M)); print('subperm check %.1e'%max(abs(w[IDX[3][S]]-perm(M[:,list(S)])) for S in SUB[3]))
# (i) w in A_3, v' in A_1: w v' = 0 <=> B v' = 0
w=rng.normal(size=10)+0j; v=rng.normal(size=5)
B=np.zeros((5,5),complex)
for j,l in PAIRS: B[j,l]=B[l,j]=w[IDX[3][tuple(c for c in R5 if c not in (j,l))]]
wv=mul(w,3,lin(v),1); print('(i) %.1e'%max(abs(wv[IDX[4][tuple(c for c in R5 if c!=m)]]-(B@v)[m]) for m in R5))
# Lefschetz: multiplication by a zero-free v: A_2 -> A_3 injective; kernel dims for sparser v
def multmat(v,k):
    return np.array([mul(np.eye(len(SUB[k]))[i],k,lin(v),1) for i in range(len(SUB[k]))]).T
for supp in (5,4,3,2):
    v=np.zeros(5); v[:supp]=rng.normal(size=supp); print('  |supp v|=%d: dim ker(v: A_2->A_3) = %d'%(supp,10-rank(multmat(v,2))))
# (ii) {v: Qv=0} has dim <= 2 for Q != 0
Q=rng.normal(size=10)+0j
Mq=np.array([mul(Q,2,np.eye(5)[j]+0j,1) for j in R5]).T; print('(ii) random Q: dim{v: Qv=0} =',5-rank(Mq))
x=np.zeros((2,5)); x[0,:3]=[1,2,-3]; x[1,:3]=[1,-1,0]; Qx=prodrows(list(x))
Mq=np.array([mul(Qx,2,np.eye(5)[j]+0j,1) for j in R5]).T; print('    Q = X_aX_b supported in 3 columns: dim{v: Qv=0} =',5-rank(Mq))
# Lemma T mechanism: K = {Q in A_2: Q.Pc.Pd = Q.Pc.Pe = Q.Pd.Pe = 0}
def Kdim(Pc,Pd,Pe):
    rows=[]
    for (P,Pp) in ((Pc,Pd),(Pc,Pe),(Pd,Pe)):
        for v in P:
            for vp in Pp:
                vv=mul(lin(v),1,lin(vp),1)
                rows.append(np.array([mul(np.eye(10)[i]+0j,2,vv,2) for i in range(10)]).T)
    return 10-rank(np.concatenate(rows))
P=[rng.normal(size=(2,5)) for _ in range(3)]
print('Lemma T: random planes: dim K =',Kdim(*P),'; Pc = Pd:',Kdim(P[0],P[0],P[2]),'; all equal:',Kdim(P[0],P[0],P[0]))
# Petersen: (A+I) n = 2*1 has only the solution n = 1/2
A=np.array([[1.0 if not set(S)&set(T) else 0.0 for T in PAIRS] for S in PAIRS])
print('Petersen eigenvalues of A+I:',sorted(set(np.round(np.linalg.eigvalsh(A+np.eye(10)),6))),' solution n =',np.round(np.linalg.solve(A+np.eye(10),2*np.ones(10)),6)[:3])
