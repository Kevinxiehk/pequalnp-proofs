# EXACT certificate for "dim T_1(M*) = 8 for all parameters".
# W = {column 0 = y (5 free entries); row c += a_c X_c, row d += a_d X_d, row e += a_e X_e on columns 1..4} (8-dim), W_7 = W cap {sum y = 0}.
# For t in C^{5x5}:  <C(J+w), t> = 24 tau_0 + sum_k (1 + y_k) Q_k^t(a),  tau_0 = sum_i t_i0,
#   Q_k^t(a) = sum_{i != k} sum_{j=1..4} t_ij H^j_ik(a),  H^j_ik = perm_3(N without rows i,k and column j),  N = 5x4 matrix of the columns 1..4.
# This script (rational arithmetic, polynomials in a_c,a_d,a_e as dicts):
#  (s1) checks perm_4(N without row i) = 24 identically (so C_i0 = 24);
#  (s2) checks that Q_c, Q_d, Q_e do not involve a_c, a_d, a_e respectively and that all Q_k are multilinear;
#  (s3) dim T_1(W_7) = dim {t : Q_k^t = -(24/5) tau_0 for all k};
#  (s4) the space T' and the image of Lambda: t -> (linear part of Q_a, linear part of Q_b) needed for the stratum m_a = m_b = 0.
import itertools, sys
from fractions import Fraction as Fr
sys.path.insert(0,'/home/claude/work/L-gct-210/stage2'); import exactla
def padd(p,q,c=1):
    r=dict(p)
    for k,v in q.items():
        r[k]=r.get(k,0)+c*v
        if r[k]==0: del r[k]
    return r
def pmul(p,q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=tuple(x+y for x,y in zip(k1,k2)); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v!=0}
one={(0,0,0):Fr(1)}
def var(i,c=1):
    k=[0,0,0]; k[i]=1; return {tuple(k):Fr(c)}
Xc=[1,0,0,-1]; Xd=[1,-1,-1,1]; Xe=[0,1,-1,0]
N=[[one]*4,[one]*4,[padd(one,var(0,Xc[t])) if Xc[t] else one for t in range(4)],[padd(one,var(1,Xd[t])) for t in range(4)],[padd(one,var(2,Xe[t])) if Xe[t] else one for t in range(4)]]
def permpoly(rows,cols):
    tot={}
    for p in itertools.permutations(cols):
        term=one
        for r,c in zip(rows,p): term=pmul(term,N[r][c])
        tot=padd(tot,term)
    return tot
# (s1)
ok=all(permpoly([r for r in range(5) if r!=i],range(4))=={(0,0,0):Fr(24)} for i in range(5)); print('(s1) perm_4(N without row i) = 24 identically for all i:',ok)
H={}
for i in range(5):
    for k in range(5):
        if i==k: continue
        for j in range(4):
            H[(i,k,j)]=permpoly([r for r in range(5) if r not in (i,k)],[c for c in range(4) if c!=j])
monos=[m for m in itertools.product((0,1),repeat=3)]
ml=all(set(h.keys())<=set(monos) for h in H.values()); print('(s2) all H^j_ik multilinear:',ml)
dep=[all(m[k-2]==0 for (i,kk,j),h in H.items() if kk==k for m in h) for k in (2,3,4)]; print('(s2) Q_c, Q_d, Q_e independent of a_c, a_d, a_e resp.:',dep)
# linear map t (25 entries, index 5*i+col, col 0..4) -> coefficients of Q_k (k=0..4, 8 monomials)
def Qcoef(k,m):
    row=[Fr(0)]*25
    for i in range(5):
        if i==k: continue
        for j in range(4): row[5*i+j+1]+=H[(i,k,j)].get(m,Fr(0))
    return row
tau0=[Fr(1) if c%5==0 else Fr(0) for c in range(25)]
def rank(rows):
    R=exactla.rref([list(r) for r in rows]); R=R[0] if isinstance(R,tuple) else R
    return sum(1 for r in R if any(x!=0 for x in r))
# (s3) T_1(W_7): nonconstant coefficients vanish, constant + 24/5 tau_0 = 0
eqs=[]
for k in range(5):
    for m in monos:
        row=Qcoef(k,m)
        if m==(0,0,0): row=[x+Fr(24,5)*y for x,y in zip(row,tau0)]
        eqs.append(row)
rk=rank(eqs); print('(s3) rank of the conditions for T_1(W_7):',rk,' => dim T_1(W_7) =',25-rk)
# (s4) T': as (s3) but the LINEAR coefficients of Q_a, Q_b (k = 0,1) are not required to vanish
lin=[(1,0,0),(0,1,0),(0,0,1)]
eqs2=[]
for k in range(5):
    for m in monos:
        if k in (0,1) and m in lin: continue
        row=Qcoef(k,m)
        if m==(0,0,0): row=[x+Fr(24,5)*y for x,y in zip(row,tau0)]
        eqs2.append(row)
rk2=rank(eqs2); print("(s4) dim T' =",25-rk2)
Tp=exactla.nullspace(eqs2,25)[0]                    # basis of T'
Lam=[[sum(Qcoef(k,m)[c]*v[c] for c in range(25)) for k in (0,1) for m in lin] for v in Tp]
R=exactla.rref([list(r) for r in Lam]); R=R[0] if isinstance(R,tuple) else R
img=[r for r in R if any(x!=0 for x in r)]
print("(s4) image of Lambda (rows: (lin Q_a | lin Q_b) in the coordinates (a_c,a_d,a_e)):")
for r in img: print('    ',[str(x) for x in r])
# explicit basis of T_1(W_7) for the record: W_7 (7 dims) + one more direction
T1=exactla.nullspace(eqs,25)[0]
ext=[Fr(1) if c%5==0 else Fr(0) for c in range(25)]; ext=[x-Fr(1,5) for x in ext]            # 1 e_0^T - J/5
inT1=all(sum(a*b for a,b in zip(row,ext))==0 for row in eqs); print('1 e_0^T - J/5 lies in T_1(W_7):',inT1)
