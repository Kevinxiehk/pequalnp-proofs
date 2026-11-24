# EXACT (rational arithmetic) certificate for T_1 and Omega of an integer 4x5 level space M (embedded with zero row 4):
#  rows of A = cof(J + (Y;0)) at integer points Y of M.  rank_Q(A) = R  =>  dim T_1(M) <= 25 - R, and T_1(M) lies in ker A.
#  If moreover explicit elements of ker A are verified to lie in T_1(M) at MORE than deg-many points ... we only need the upper bound:
#  Omega(M) lies in the row-4 projection of ker A.
import sys, itertools, random
from fractions import Fraction as Fr
P4=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0][p[0]]*A[1][p[1]]*A[2][p[2]]*A[3][p[3]] for p in P4)
def cof(M):
    out=[]
    for i in range(5):
        for j in range(5):
            A=[[M[a][b] for b in range(5) if b!=j] for a in range(5) if a!=i]; out.append(perm4(A))
    return out
def nullspace(A,ncol):
    A=[row[:] for row in A]; piv=[]; r=0
    for c in range(ncol):
        p=next((i for i in range(r,len(A)) if A[i][c]!=0),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r]; inv=1/A[r][c]; A[r]=[v*inv for v in A[r]]
        for i in range(len(A)):
            if i!=r and A[i][c]!=0:
                f=A[i][c]; A[i]=[a-f*b for a,b in zip(A[i],A[r])]
        piv.append(c); r+=1
        if r==len(A): break
    free=[c for c in range(ncol) if c not in piv]; N=[]
    for f in free:
        v=[Fr(0)]*ncol; v[f]=Fr(1)
        for k,c in enumerate(piv): v[c]=-A[k][f]
        N.append(v)
    return r,N
def certificate(B,name,npts=260,seed=1):
    random.seed(seed); d=len(B); rows=[]
    for _ in range(npts):
        c=[random.randint(-4,4) for _ in range(d)]
        M=[[Fr(1)+sum(c[k]*B[k][i][j] for k in range(d)) if i<4 else Fr(1) for j in range(5)] for i in range(5)]
        g=cof(M); assert sum(M[4][j]*g[20+j] for j in range(5))==120, 'not level'
        rows.append(g)
    R,N=nullspace(rows,25)
    # row-4 projection of ker A
    proj=[v[20:] for v in N]; r2,_=nullspace([list(x) for x in zip(*proj)],len(proj)) if proj else (0,[])
    rp,_n=nullspace(proj,5); 
    print('%s: exact level at %d integer points; rank_Q of gradient span >= %d  =>  dim T_1 <= %d; row-4 projection of ker has dim %d'%(name,npts,R,25-R,rp))
    # is the projection inside span(1, e_c)?  report its orthogonal complement
    print('   vectors orthogonal to the projection (=> lie in Omega^perp):',[[str(x) for x in v] for v in _n])
if __name__=='__main__':
    Z=lambda: [[Fr(0)]*5 for _ in range(4)]
    def E(cells):
        m=Z()
        for (i,j,v) in cells: m[i][j]=Fr(v)
        return m
    w0=[1,-1,0,0]; w1=[0,0,1,-1]; w3=[1,1,-1,-1]
    B=[E([(0,0,1),(2,0,-1)]),E([(1,0,1),(2,0,-1)]),E([(3,0,1),(2,0,-1)]),
       E([(0,1+c,w0[c]) for c in range(4)]),E([(1,1+c,w1[c]) for c in range(4)]),E([(3,1+c,w3[c]) for c in range(4)])]
    certificate(B,'fam_nc member w0=(1,-1,0,0), w1=(0,0,1,-1), w3=(1,1,-1,-1)')
    # L080 row-0 kernel (integer if core.SP['L080'] is integer)
    sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
    try:
        import core, numpy as np
        from t import sub_supported
        Bm=np.array([np.array(mm,dtype=complex) for mm in core.SP['L080']()])
        order=[1,2,3,4,0]; Bp=Bm[:,order,:]; mk=np.ones((5,5),bool); mk[4]=False
        S=sub_supported(Bp,mk)[:,:4,:]
        # integer basis via rref with rational reconstruction
        A=[[Fr(float(v.real)).limit_denominator(1000) for v in m.ravel()] for m in S]
        r,_=nullspace([row[:] for row in A],20)
        # rref rows
        Ar=[row[:] for row in A]; piv=[]; rr=0
        for c in range(20):
            p=next((i for i in range(rr,len(Ar)) if abs(Ar[i][c])>Fr(1,10**6)),None)
            if p is None: continue
            Ar[rr],Ar[p]=Ar[p],Ar[rr]; inv=1/Ar[rr][c]; Ar[rr]=[(v*inv).limit_denominator(1000) for v in Ar[rr]]
            for i in range(len(Ar)):
                if i!=rr and Ar[i][c]!=0:
                    f=Ar[i][c]; Ar[i]=[(a-f*b).limit_denominator(1000) for a,b in zip(Ar[i],Ar[rr])]
            rr+=1
            if rr==len(Ar): break
        B2=[[row[5*i:5*i+5] for i in range(4)] for row in Ar[:rr]]
        certificate(B2,'L080 row-0 kernel (rational rref basis)')
    except AssertionError as ex:
        print('L080 kernel: rational reconstruction failed:',ex)
