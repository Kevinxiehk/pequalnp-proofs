# verify2: exact checks for verifyfl's TC5.
# (F1) Res_u(E_t, P_t) = -(3/256) (t^8 - 56 t^4 + 16)^3,  E_t(u) = (t^3/2) u^2 + (1 + t^4/4) u + 2t,
#      P_t(u) = 2 (t^2 + 4tu + u^2)^2 - (3/2) (t^2 u^2 - 4)^2.   Both sides are polynomials in t of degree <= 32; compare at 60 rational points.
# Also: closed forms tau(v(t)^2 v(u)) = 4 E_t(u) and [v,v,v',v'] = P_t(u) from the definitions (own derivation), exact Gaussian arithmetic.
from fractions import Fraction as Fr
import itertools
def det(M):
    M=[r[:] for r in M]; n=len(M); d=Fr(1)
    for c in range(n):
        p=next((i for i in range(c,n) if M[i][c]!=0),None)
        if p is None: return Fr(0)
        if p!=c: M[c],M[p]=M[p],M[c]; d=-d
        d*=M[c][c]
        for i in range(c+1,n):
            f=M[i][c]/M[c][c]
            if f!=0: M[i]=[x-f*y for x,y in zip(M[i],M[c])]
    return d
def polyE(t): return [t**3/2, 1+t**4/4, 2*t]                 # coefficients of u^2, u^1, u^0
def polyP(t):
    # 2(t^2+4tu+u^2)^2 - (3/2)(t^2u^2-4)^2 as polynomial in u (degree 4): coefficients u^4..u^0
    a=[Fr(1),4*t,t*t]                     # u^2 + 4t u + t^2
    sq=[Fr(0)]*5
    for i in range(3):
        for j in range(3): sq[i+j]+=a[i]*a[j]
    b=[t*t,Fr(0),Fr(-4)]                  # t^2 u^2 - 4
    sq2=[Fr(0)]*5
    for i in range(3):
        for j in range(3): sq2[i+j]+=b[i]*b[j]
    return [2*x-Fr(3,2)*y for x,y in zip(sq,sq2)]
def sylv(f,g):
    m=len(f)-1; n=len(g)-1; N=m+n; M=[]
    for i in range(n): M.append([Fr(0)]*i+f+[Fr(0)]*(N-m-1-i))
    for i in range(m): M.append([Fr(0)]*i+g+[Fr(0)]*(N-n-1-i))
    return M
bad=0; pts=[Fr(k,d) for k in range(-15,16) for d in (1,3) if k!=0][:60]
for t in pts:
    r=det(sylv(polyE(t),polyP(t))); claim=-Fr(3,256)*(t**8-56*t**4+16)**3
    if r!=claim: bad+=1
print('(F1) resultant identity: %d rational points tested, mismatches: %d'%(len(pts),bad))
# closed forms from the definitions, with exact Gaussian rationals
class G:
    def __init__(s,a=0,b=0): s.a=Fr(a); s.b=Fr(b)
    def __add__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __sub__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a-o.a,s.b-o.b)
    def __mul__(s,o): o=o if isinstance(o,G) else G(o); return G(s.a*o.a-s.b*o.b,s.a*o.b+s.b*o.a)
    __rmul__=__mul__
    def __eq__(s,o): o=o if isinstance(o,G) else G(o); return s.a==o.a and s.b==o.b
I=G(0,1); pw=[G(1),I,G(-1),G(0,-1)]
chi=lambda a:[pw[(a*k)%4] for k in range(4)]
def vec(t): return [chi(1)[k]+t*chi(2)[k]+(-t*t/2)*chi(3)[k] for k in range(4)]
def tau(*vs):
    s=G(0)
    for k in range(4):
        p=G(1)
        for v in vs: p=p*v[k]
        s=s+p
    return s
def br(a,b,c,d): return G(-6)*tau(a,b,c,d)+tau(a,b)*tau(c,d)+tau(a,c)*tau(b,d)+tau(a,d)*tau(b,c)
bad2=0; n=0
for t in [Fr(k,2) for k in range(-5,6)]:
    for u in [Fr(k,3) for k in range(-5,6)]:
        v=vec(t); w=vec(u); n+=1
        E=polyE(t); Ev=E[0]*u*u+E[1]*u+E[2]
        P=polyP(t); Pv=sum(c*u**(4-i) for i,c in enumerate(P))
        if not (tau(v,v)==0 and tau(v)==0 and tau(v,v,w)==4*Ev and br(v,v,w,w)==Pv): bad2+=1
print('closed forms tau(v^2 v\') = 4 E_t(u), [v,v,v\',v\'] = P_t(u), v(t) isotropic in V: %d points, mismatches: %d'%(n,bad2))
# perm[h,h,zeta_0,conj zeta_0] = 6 and 3 tau(chi_1^2 chi_3^2) - <chi_1,chi_3>^2 = -4, [chi_3,chi_3,chi_1,chi_1] = 8, [chi_2]^4 bracket = 24
import cmath
w=cmath.exp(2j*cmath.pi/3); h=[1,1,1,-1]; z0=[1,w,w*w,0]; z0b=[1,w*w,w,0]
pm=sum(h[p[0]]*h[p[1]]*z0[p[2]]*z0b[p[3]] for p in itertools.permutations(range(4)))
print('perm[h,h,zeta_0,conj zeta_0] =',round(pm.real,10),'+',round(pm.imag,10),'i')
c1,c2,c3=chi(1),chi(2),chi(3)
t13=tau(c1,c1,c3,c3); g=tau(c1,c3)
print('3 tau(chi_1^2 chi_3^2) - <chi_1,chi_3>^2 =',(G(3)*t13-g*g).a,' [chi_3,chi_3,chi_1,chi_1] =',br(c3,c3,c1,c1).a,' [chi_2,chi_2,chi_2,chi_2] =',br(c2,c2,c2,c2).a)
