from fractions import Fraction as Fr
import itertools
def rref(M):
    M=[[Fr(x) for x in r] for r in M]; piv=[]; r=0; nc=len(M[0]) if M else 0
    for c in range(nc):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i; break
        if p is None: continue
        M[r],M[p]=M[p],M[r]; pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==len(M): break
    return M,piv
def nullspace(M,nc):
    R,piv=rref(M); free=[c for c in range(nc) if c not in piv]; ns=[]
    for f in free:
        v=[Fr(0)]*nc; v[f]=Fr(1)
        for i,c in enumerate(piv): v[c]=-R[i][f]
        ns.append(v)
    return ns,len(piv)
def perm(A):
    m=len(A); s=Fr(0)
    for p in itertools.permutations(range(m)):
        t=Fr(1)
        for i in range(m):
            t*=A[i][p[i]]
            if t==0: break
        s+=t
    return s
