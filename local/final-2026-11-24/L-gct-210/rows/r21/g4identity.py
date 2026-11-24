# Numerical check of the G4-A plane identities (R21.9): 5 columns, be_5 = 0 (n-column 5 zero), w = al_5 c(t5) (plane column 5 = (u-w)/2),
# sum_{k<=4} be_k c_k = 0, sum_{k<=4} al_k c_k = 3u - w.  For j <= 4, R = [4]\j, v = 2u - w:
#   ka^3(8 D_j) = -be_R C_R
#   ka^2(8 D_j) = -1/2 sum_{a<=4} be_a^2 B^v_aa + be_j^2 B^v_jj - (cyc al be be)_R C_R
#   ka^1(8 D_j) = -be_j l(c_j) - sum_{a<=4} al_a be_a B^v_aa + 2 al_j be_j B^v_jj - (cyc al al be)_R C_R,
#   l(x) = 3K(x,u,u) - 3K(x,u,w) + K(x,w,w).
import random, itertools, numpy as np
def c(s): return np.array([s*s-1, 1j*(s*s+1), 2*s])
def K(a,b,d): return sum(a[p[0]]*b[p[1]]*d[p[2]] for p in itertools.permutations(range(3)))
random.seed(3); worst=0
for trial in range(20):
    r=[complex(random.gauss(0,1),random.gauss(0,1)) for _ in range(7)]
    s0,S,t5,al5=r[0],r[1:5],r[5],r[6]
    u=c(s0); C=[c(x) for x in S]; w=al5*c(t5); v=2*u-w
    M=np.array([C[1],C[2],C[3]]).T
    be=[1]+list(np.linalg.solve(M,-C[0])); al=[0]+list(np.linalg.solve(M,3*u-w))
    cols=lambda ka:[(u-(al[i]+ka*be[i])*C[i])/2 for i in range(4)]+[(u-w)/2]
    Bv=[K(C[a],C[a],v) for a in range(4)]
    for j in range(4):
        S5=[i for i in range(5) if i!=j]
        def D(ka):
            Y=cols(ka); return 8*sum(K(Y[a],Y[b],Y[d]) for a,b,d in itertools.combinations(S5,3))
        pts=np.array([0,1,2,3],dtype=complex); coef=np.linalg.solve(np.vander(pts,4,increasing=True),np.array([D(x) for x in pts]))
        R=[i for i in range(4) if i!=j]; a,b,d=R; CR=K(C[a],C[b],C[d])
        cyc1=al[a]*be[b]*be[d]+be[a]*al[b]*be[d]+be[a]*be[b]*al[d]
        cyc2=al[a]*al[b]*be[d]+al[a]*be[b]*al[d]+be[a]*al[b]*al[d]
        l=lambda x:3*K(x,u,u)-3*K(x,u,w)+K(x,w,w)
        k3=-be[a]*be[b]*be[d]*CR
        k2=-0.5*sum(be[i]**2*Bv[i] for i in range(4))+be[j]**2*Bv[j]-cyc1*CR
        k1=-be[j]*l(C[j])-sum(al[i]*be[i]*Bv[i] for i in range(4))+2*al[j]*be[j]*Bv[j]-cyc2*CR
        sc=max(1,*abs(coef[1:]))
        worst=max(worst,abs(coef[3]-k3)/sc,abs(coef[2]-k2)/sc,abs(coef[1]-k1)/sc)
print('G4-A closed forms, max relative deviation:',worst)
