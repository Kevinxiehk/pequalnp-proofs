# verify2: INDEPENDENT re-implementation (own enumeration, floating point with O(1) margins) of stage2's T1 tests (t5_triple_all, t10_typeII_exact).
# Rows 1,2,3; tau-coordinates; pair (i,i') structures:
#   Type I : partition {C, C^c}; kappa^i' = c w kappa^i, w = +1 on C, -1 off C; relation  sum_C tau_i - sum_C tau_i' = s ell
#   Type II: (Q1,Q2,Q3,eps); w = eps*i on Q1, 1 on Q2, -1 on Q3;               relation  sum_Q3 tau_i + sum_Q2 tau_i' = -y ell, y = (-1+eps i)/2
import itertools, numpy as np
rng=np.random.default_rng(0)
def structures():
    out=[]
    for bits in itertools.product([0,1],repeat=5):
        if bits[0]!=1 or sum(bits)==5: continue
        C=np.array(bits); out.append(('I',np.where(C==1,1,-1).astype(complex),C.astype(complex),-C.astype(complex),None))
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        q=np.array(cells)
        for eps in (1,-1):
            w=np.where(q==0,eps*1j,np.where(q==1,1,-1)).astype(complex)
            out.append(('II',w,(q==2).astype(complex),(q==1).astype(complex),(-1+eps*1j)/2))
    return out
ALL=structures()
def canon():
    out=[]
    for C in ([1,0,0,0,0],[1,1,0,0,0]):
        C=np.array(C); out.append(('I',np.where(C==1,1,-1).astype(complex),C.astype(complex),-C.astype(complex),None))
    for comp in itertools.product(range(1,4),repeat=3):
        if sum(comp)!=5: continue
        q=np.array([0]*comp[0]+[1]*comp[1]+[2]*comp[2]); w=np.where(q==0,1j,np.where(q==1,1,-1)).astype(complex)
        out.append(('II',w,(q==2).astype(complex),(q==1).astype(complex),(-1+1j)/2))
    return out
def prop(a,b):
    r=a/b; return np.allclose(r,r[0])
def perm3(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]] for p in itertools.permutations(range(3)))
def rank(A,tol=1e-9):
    s=np.linalg.svd(A,compute_uv=False); return int(np.sum(s>tol))
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int(np.sum(s>tol)); return vh[r:].conj().T
stats={}; surv=[]
for s12 in canon():
    for s13 in ALL:
        ratio=s13[1]/s12[1]
        opts=[s for s in ALL if prop(ratio,s[1])]
        key=(s12[0],s13[0])
        if not opts: stats[key+('inadmissible',)]=stats.get(key+('inadmissible',),0)+1; continue
        for s23 in opts:
            F=np.zeros((6,15),complex)
            for i in range(3): F[i,5*i:5*i+5]=1
            F[3,0:5]=s12[2]; F[3,5:10]=s12[3]
            F[4,0:5]=s13[2]; F[4,10:15]=s13[3]
            F[5,5:10]=s23[2]; F[5,10:15]=s23[3]
            W=np.array([np.ones(5,complex),s12[1],s13[1]])
            killed=False
            for S in itertools.combinations(range(5),3):
                idx=[5*i+j for i in range(3) for j in S]
                FS=F[:,idx]
                if rank(FS)<6: continue
                N=null(FS)
                for _ in range(3):
                    tau=(N@(rng.normal(size=N.shape[1])+1j*rng.normal(size=N.shape[1]))).reshape(3,3)
                    if abs(perm3(tau/W[:,list(S)]))>1e-6*np.abs(tau).max()**3: killed=True; break
                if killed: break
            k=key+((s23[0],'killed' if killed else 'SURVIVES'),)
            stats[k]=stats.get(k,0)+1
            if not killed: surv.append((s12,s13,s23))
for k,v in sorted(stats.items(),key=str): print(k,v)
# full cube test for the survivors (all Type II: constants universal)
res={'killed (perm_3 != k ell^3 on some Pi_S with ell != 0)':0,'survive':0,'N rank < 5':0}; left=[]
for s12,s13,s23 in surv:
    assert s12[0]==s13[0]==s23[0]=='II'
    N5=np.zeros((5,15),complex)
    N5[0,0:5]=1; N5[0,5:10]=-1; N5[1,0:5]=1; N5[1,10:15]=-1
    N5[2,0:5]=s12[2]+s12[4]; N5[2,5:10]=s12[3]
    N5[3,0:5]=s13[2]+s13[4]; N5[3,10:15]=s13[3]
    N5[4,5:10]=s23[2]+s23[4]; N5[4,10:15]=s23[3]
    if rank(N5)<5: res['N rank < 5']+=1
    W=np.array([np.ones(5,complex),s12[1],s13[1]]); killed=False
    for S in itertools.combinations(range(5),3):
        idx=[5*i+j for i in range(3) for j in S]
        K=null(N5[:,idx])
        if K.shape[1]==0: continue
        ell=K[0:3,:].sum(axis=0)          # row-1 sum on S
        if np.abs(ell).max()<1e-9: continue
        vals=[]
        for _ in range(4):
            c=rng.normal(size=K.shape[1])+1j*rng.normal(size=K.shape[1]); tau=(K@c).reshape(3,3); e=tau[0].sum()
            vals.append(perm3(tau/W[:,list(S)])/e**3)
        if max(abs(v-vals[0]) for v in vals)>1e-6*max(1,abs(vals[0])): killed=True; break
    if killed: res['killed (perm_3 != k ell^3 on some Pi_S with ell != 0)']+=1
    else: res['survive']+=1; left.append((s12,s13,s23))
print(res)
for s12,s13,s23 in left:
    f=lambda s: ''.join('ABC'[k] for k in [0 if abs(x-s[1][np.argmax(np.abs(s[1].imag))])<1e-9 and abs(x.imag)>0.5 else (1 if abs(x-1)<1e-9 else 2) for x in s[1]])
    print('  survivor: (Q-pattern 12, 13, 23) [A=Q1,B=Q2,C=Q3]:',f(s12),f(s13),f(s23),' eps:',int(round(s12[1][np.argmax(np.abs(s12[1].imag))].imag)),int(round(s13[1][np.argmax(np.abs(s13[1].imag))].imag)),int(round(s23[1][np.argmax(np.abs(s23[1].imag))].imag)))
