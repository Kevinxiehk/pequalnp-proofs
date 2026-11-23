import numpy as np, itertools
w=np.exp(2j*np.pi/5); chi=lambda k: w**(k*np.arange(5))
Chi=np.array([chi(c) for c in range(5)]).T
def F(p):  # matrix of quadratic form v -> [eps^2] prod(p_c+eps v_c) = sum_{j<l} v_j v_l prod_{c not in{j,l}} p_c
    M=np.zeros((5,5),complex)
    for j in range(5):
        for l in range(5):
            if j!=l: M[j,l]=np.prod([p[c] for c in range(5) if c not in (j,l)])/2
    return M
def coeffs(a,b):
    # forms as cubic polynomial in (s,t): p = s chi_a + t chi_b; extract coefficient of s^i t^(3-i) by interpolation
    pts=[(np.exp(2j*np.pi*m/4)) for m in range(4)]
    out={}
    vals=[Chi.T@F(chi(a)*1+chi(b)*r)@Chi for r in pts]   # s=1, t=r : sum_i C_i r^(3-i)
    for e in range(4):  # coefficient of t^e
        C=sum(vals[m]*pts[m]**(-e) for m in range(4))/4
        C[abs(C)<1e-9]=0; out[e]=C
    return out
for (a,b) in [(1,4),(2,3)]:
    out=coeffs(a,b)
    for e in range(4):
        C=out[e]; nz=[(i,j,np.round(C[i,j]*(1 if i==j else 2),6)) for i in range(5) for j in range(i,5) if C[i,j]!=0]
        print('p=chi%d+t chi%d, coeff t^%d:'%(a,b,e),nz)
