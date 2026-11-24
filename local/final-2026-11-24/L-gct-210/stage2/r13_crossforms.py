# Forms P_2 and B_z on T_1(X)/X for the cross-type family (r13_crossfam.py), in coordinates
#   sig = t10+t20+t30, s4 = sum_l t4l, ph4 = sum_{k>=1} a_k t4k, u1..u4 (common entries of rows 1-3 in columns 1..4), t04.
# The representative t of a class: col0 rows1-3 = (sig,0,0); row 4 = s4*e0 + ph4-adjusted vector; t00, t01..t03 from the T_1 equations.
import sys, itertools, sympy as sp
a1,a2,a3=sp.symbols('a1 a2 a3'); a=[a1,a2,a3,sp.Integer(1)]
sig,s4,ph4,u1,u2,u3,u4,t04=sp.symbols('sig s4 ph4 u1 u2 u3 u4 t04'); u=[u1,u2,u3,u4]
D=a1+a2+a3-4
# row 4 representative r4 = (x0, x1..x4) with sum = s4 and sum_k a_k x_k = ph4: take x = alpha*e0 + beta*e4  (a4 = 1): beta = ph4, alpha = s4 - ph4
r4=[s4-ph4,0,0,0,ph4]
t=sp.zeros(5,5)
t[1,0]=sig
for k in (1,2,3):
    for j in range(1,5): t[k,j]=u[j-1]
for j in range(5): t[4,j]=r4[j]
t[0,4]=t04
S4=sum(r4)
# T_1 equations (from r13_crossfam.py output):
t[0,1]=-( (4*a1-a2-a3-1)/D*t04 + 3*u1 + 3*(4*a1-a2-a3-1)/D*u4 + (a1-1)/D*S4 )
t[0,2]=-( -(a1-4*a2+a3+1)/D*t04 + 3*u2 - 3*(a1-4*a2+a3+1)/D*u4 + (a2-1)/D*S4 )
t[0,3]=-( -(a1+a2-4*a3+1)/D*t04 + 3*u3 - 3*(a1+a2-4*a3+1)/D*u4 + (a3-1)/D*S4 )
t[0,0]=-( -(a1+a2+a3+1)/D*t04 + sig + -3*(a1+a2+a3+1)/D*u4 - 1/D*S4 )
def P2(M):
    n=M.rows; tot=0
    for i,k in itertools.combinations(range(n),2):
        for j in range(M.cols):
            for l in range(M.cols):
                if j!=l: tot+=M[i,j]*M[k,l]
    return sp.expand(tot)
q0=sp.factor(P2(t))
tau=t[0:4,:]
def P2cols(M,cols):
    sub=M.extract(list(range(M.rows)),cols); return P2(sub)
pj=[sp.expand(P2cols(tau,[c for c in range(5) if c!=j])) for j in range(5)]
# B_z for z in Z: z^(k) = (-(1-a_k); e_k - a_k e_4) for k = 1,2,3
Bz=[]
for k in range(3):
    zz=[-(1-a[k])]+[1 if c==k else 0 for c in range(4)]; zz[4]=zz[4]-a[k]
    Bz.append(sp.factor(sp.expand(4*sum(zz[j]*pj[j] for j in range(5)))))
print('P_2 =',q0); 
for k in range(3): print('B_z%d ='%(k+1),Bz[k])
