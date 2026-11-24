# Round 17: z = (1,1,1,1,0), configuration "three rows m (e_1=e_2=e_3=0) + one row w = omega(m) (orthogonal to 1, m, m^2, m^3)" (covers k_N = 1
# and the (3,1) distribution of k_N = 0). Regime needs dim X_{rk} >= 3 for all pairs r,k in S. For each pair: the alpha-linear conditions on
# xi = (v row 4; a row l; b row n) (rows 0-indexed: S = {0,1,2,3}, row 4 has no single-row vector), kernel modulo the gauge (a in C w_l, b in C w_n).
import numpy as np, itertools
def sig(M,m,cols):
    tot=0
    for R in itertools.combinations(range(M.shape[0]),m):
        for C in itertools.permutations(cols,m): tot=tot+np.prod([M[R[k],C[k]] for k in range(m)])
    return tot
def delv(W):
    t=W.shape[0]
    if t==0: return np.ones(5,complex)
    return np.array([sig(W,t,[c for c in range(5) if c!=j]) for j in range(5)])
rg=np.random.default_rng(4)
for trial in range(3):
    a4=rg.normal()+1j*rg.normal(); a5=rg.normal()+1j*rg.normal()
    m=np.roots([1,0,0,0,a4,a5])                       # x^5 + a4 x + a5: e_1 = e_2 = e_3 = 0
    V=np.array([m**t for t in range(4)]); u,s,vh=np.linalg.svd(V); w=vh[-1].conj()   # w orthogonal (bilinear) to 1, m, m^2, m^3
    w=vh[-1]; w=np.linalg.svd(V)[2][-1].conj()
    # bilinear orthogonality: solve V w = 0
    w=np.linalg.svd(V)[2][-1].conj(); 
    ns=np.linalg.svd(V)[2]; w=ns[-1].conj()
    print('trial',trial,' |V w| =',np.abs(V@w).max(),' <w,w> =',np.round(w@w,4),' isotropic? (needed only for k_N = 0)')
    rows_sr=[m,m,m,w]
    for r,k in itertools.combinations(range(4),2):
        l,n=[i for i in range(4) if i not in (r,k)]; A=[]
        for t in range(5):
            for T in itertools.combinations(range(4),t):
                Dv=delv(np.array([rows_sr[i] for i in T]).reshape(len(T),5))
                A.append(np.concatenate([Dv,Dv*(l not in T),Dv*(n not in T)]))
        A=np.array(A); sv=np.linalg.svd(A,compute_uv=False); kd=15-int((sv>1e-9*sv[0]).sum())
        print('   pair (r,k)=(%d,%d): rows l,n = %d,%d carry %s; kernel dim %d (gauge 2)'%(r,k,l,n,('m' if l<3 else 'w')+('m' if n<3 else 'w'),kd))
