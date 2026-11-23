# Round 3: LEMMA Y5.  y a 2-row element (rows a,b), c a third row with pi_c(L^) = C^5, j a column with kappa^c_j != 0.
# On V_cj = {u in L^ : u_c in C e_j}: perm_4((y_a, y_b, u_d, u_e) minus column j) = 0, i.e. u_d^T B u_e = 0 with
# B[p,q] = Q_y[F - {p,q}], F = [5] - j.  Hence rank B <= 8 - dim W = 2 + m_ab (W = image of V_cj in rows d,e, columns F).
# (i) identity AB+AC+BC = e1 e3 - 4 e4; (ii) no five nonzero numbers with (sum r)(sum 1/r) = 4 on all five 4-subsets (LM search);
# (iii) sanity of the identity/isotropy and of the rank bound on the exact examples.
import sys, itertools, numpy as np
sys.path.insert(0,'/home/claude/work/L-gct-210/chief'); sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from core import SP, perm
from pairlib import nullspace, rank
from scipy.optimize import least_squares
rng=np.random.default_rng(6)
def rnd(*k): return rng.normal(size=k)+1j*rng.normal(size=k)
r=rnd(4); p,q,s,t=r; A=p*q+s*t; Bq=p*s+q*t; C=p*t+q*s
e1=r.sum(); e3=sum(np.prod(r[list(c)]) for c in itertools.combinations(range(4),3)); e4=np.prod(r)
print('(i) |AB+AC+BC - (e1 e3 - 4 e4)| = %.1e'%abs(A*Bq+A*C+Bq*C-(e1*e3-4*e4)))
def F5(x):
    rr=x[:5]+1j*x[5:]; out=[]
    for j in range(5):
        f=np.delete(rr,j); v=f.sum()*(1/f).sum()-4; out+=[v.real,v.imag]
    return np.array(out+[np.linalg.norm(rr)-1.5])
best=[]
for trial in range(40):
    sol=least_squares(F5,rng.normal(size=10),method='lm'); rr=sol.x[:5]+1j*sol.x[5:]; best.append((np.linalg.norm(F5(sol.x)),np.abs(rr).min()))
conv=[b for b in best if b[0]<1e-9]
print('(ii) LM for 5 numbers: %d of 40 runs reach residual < 1e-9; smallest residual %.2e; (min |r_j| among converged: %s)'%(len(conv),min(b[0] for b in best),['%.1e'%b[1] for b in conv][:5]))
tot=0; viol=0; dimdiff=0
for name,f in SP.items():
    Bs=f(); n=len(Bs); Bh=np.concatenate([np.ones((1,5,5),complex),Bs])
    arow=[5-rank(np.array([Bs[k][i] for k in range(n)])) for i in range(5)]
    for a,b in itertools.combinations(range(5),2):
        oth=[i for i in range(5) if i not in (a,b)]
        N=nullspace(np.array([[Bs[k][i,jj] for k in range(n)] for i in oth for jj in range(5)]))
        if N.shape[1]==0: continue
        Y=np.tensordot(N.T,Bs,1); mab=len(Y)
        for _ in range(2):
            y=np.tensordot(rnd(mab),Y,1)
            for c in oth:
                if arow[c]!=1: continue
                d,e=[i for i in oth if i!=c]
                for j in range(5):
                    Cm=np.array([[Bh[k][c,jj] for k in range(n+1)] for jj in range(5) if jj!=j]); V=nullspace(Cm)   # V_cj
                    if np.abs(np.array([Bh[k][c,j] for k in range(n+1)])@V).max()<1e-9: continue                   # kappa^c_j = 0
                    Fc=[jj for jj in range(5) if jj!=j]
                    Bm=np.zeros((4,4),complex)
                    for x1,x2 in itertools.combinations(range(4),2):
                        T=[Fc[k] for k in range(4) if k not in (x1,x2)]
                        Bm[x1,x2]=Bm[x2,x1]=y[a,T[0]]*y[b,T[1]]+y[a,T[1]]*y[b,T[0]]
                    W=np.array([[sum(V[k,q]*Bh[k][i,jj] for k in range(n+1)) for q in range(V.shape[1])] for i in (d,e) for jj in Fc])
                    dW=rank(W); iso=0
                    for _ in range(4):
                        w=W@rnd(V.shape[1]); iso=max(iso,abs(w[:4]@Bm@w[4:]))
                    tot+=1; ok= iso<1e-8 and rank(Bm)<=8-dW
                    viol+= (not ok); dimdiff+= (dW!=V.shape[1]-mab)
print('(iii) Lemma Y5 on the examples: cases',tot,' violations of isotropy / rank bound:',viol,' ; cases where the kernel is larger than Y_ab (rows d,e not zero-free a=1):',dimdiff)
