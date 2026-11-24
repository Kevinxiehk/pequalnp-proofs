# Numerical check of the case-G pencil identities (R21.8).  y_k(ka) = (u - (al_k + ka be_k) c(s_k))/2, sum be_k c(s_k) = 0 (be_1 = 1),
# sum al_k c(s_k) = 2u, u = c(s0); K = polarised x1 x2 x3 (= 3x3 permanent).  For each triple T = [4]\k, the ka^3, ka^2, ka^1 coefficients
# of 8 K(y_a,y_b,y_c) must equal the closed forms:
#   ka^3: -be_a be_b be_c C_T
#   ka^2: -1/2 sum_a be_a^2 B_aa + be_k^2 B_kk - (sum_cyc al_a be_b be_c) C_T
#   ka^1: -be_k A_k + 2 al_k be_k B_kk - sum_a al_a be_a B_aa - (sum_cyc al_a al_b be_c) C_T
# with A_k = K(c_k,u,u), B_ab = K(c_a,c_b,u), C_T = K(c_a,c_b,c_c).
import random, itertools, cmath
def c(s): return (s*s-1, 1j*(s*s+1), 2*s)
def K(a,b,d): return sum(a[p[0]]*b[p[1]]*d[p[2]] for p in itertools.permutations(range(3)))
def solve3(M,v):
    import copy
    A=[list(M[i])+[v[i]] for i in range(3)]
    for i in range(3):
        p=max(range(i,3),key=lambda r:abs(A[r][i])); A[i],A[p]=A[p],A[i]
        for r in range(3):
            if r!=i:
                f=A[r][i]/A[i][i]; A[r]=[A[r][j]-f*A[i][j] for j in range(4)]
    return [A[i][3]/A[i][i] for i in range(3)]
random.seed(7); worst=0
for trial in range(20):
    s=[complex(random.gauss(0,1),random.gauss(0,1)) for _ in range(5)]; s0=s[0]; S=s[1:]
    C=[c(x) for x in S]; u=c(s0)
    # be: be_1 = 1, solve be_2..4 from sum be_k c_k = 0
    M=[[C[1][i],C[2][i],C[3][i]] for i in range(3)]; b=solve3(M,[-C[0][i] for i in range(3)]); be=[1]+b
    # al: al_1 = 0, solve al_2..4 from sum al_k c_k = 2u
    a=solve3(M,[2*u[i] for i in range(3)]); al=[0]+a
    A=[K(C[k],u,u) for k in range(4)]; B=[[K(C[i],C[j],u) for j in range(4)] for i in range(4)]
    for k in range(4):
        T=[i for i in range(4) if i!=k]
        def Y(ka): return [tuple((u[r]-(al[i]+ka*be[i])*C[i][r])/2 for r in range(3)) for i in T]
        # polynomial in ka of degree 3: sample 4 points, solve Vandermonde
        pts=[0,1,2,3]; vals=[8*K(*Y(x)) for x in pts]
        # Newton divided differences -> coefficients
        import numpy as _np
        coef=_np.linalg.solve(_np.vander(_np.array(pts,dtype=complex),4,increasing=True),_np.array(vals))
        CT=K(C[T[0]],C[T[1]],C[T[2]]); a_,b_,c_=T
        cyc1=al[a_]*be[b_]*be[c_]+be[a_]*al[b_]*be[c_]+be[a_]*be[b_]*al[c_]
        cyc2=al[a_]*al[b_]*be[c_]+al[a_]*be[b_]*al[c_]+be[a_]*al[b_]*al[c_]
        k3=-be[a_]*be[b_]*be[c_]*CT
        k2=-0.5*sum(be[i]**2*B[i][i] for i in range(4))+be[k]**2*B[k][k]-cyc1*CT
        k1=-be[k]*A[k]+2*al[k]*be[k]*B[k][k]-sum(al[i]*be[i]*B[i][i] for i in range(4))-cyc2*CT
        sc=max(1,abs(coef[3]),abs(coef[2]),abs(coef[1]))
        worst=max(worst,abs(coef[3]-k3)/sc,abs(coef[2]-k2)/sc,abs(coef[1]-k1)/sc)
print('max relative deviation of the closed forms over 20 random configurations x 4 triples:',worst)
