# The degree-2/3 relaxation of (SM5) (W5 = sm5w.py ISO=1, SP5 = cubic on the conic) is NOT unit: rank-2 configuration on the Walsh
# plane x3 = 0, f = (1, i, 0) isotropic, null coordinates p = x1 + i x2, q = x1 - i x2: columns (p,q) = (t,1), (-t,1), (0,1), (0,-2), (0,1).
# Check: t^2, t^3 coefficients of perm(J + sY \ col j) - 24 vanish for all j (P_4 does not).
import itertools, numpy as np
H=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=complex)
def perm(M): return sum(np.prod([M[i][s[i]] for i in range(4)]) for s in itertools.permutations(range(4)))
def y(p,q): return np.array([(p+q)/2,(p-q)/(2j),0])
t=0.8+0.3j
ys=[y(t,1),y(-t,1),y(0,1),y(0,-2),y(0,1)]
print('f =',np.round(sum(ys),12),' f.f =',abs(sum(sum(ys)**2)))
cols=[H@v for v in ys]
for j in range(5):
    cc=[cols[k] for k in range(5) if k!=j]
    ss=np.array([0.5,1.0,1.5,2.0,2.5],dtype=complex)
    vals=[perm([[1+s*cc[k][i] for k in range(4)] for i in range(4)])-24 for s in ss]
    co=np.linalg.solve(np.vander(ss,5,increasing=True),vals)
    print('deletion',j+1,' |t^1|,|t^2|,|t^3| =',['%.1e'%abs(x) for x in co[1:4]],' t^4 =',np.round(co[4],6))
