# (alpha0), |supp W| = 4, after the reduction: W = the unique special configuration (lines omitting an opposite pair), entries in Z[i].
# K = {Y_s + mu Z}: y_j = (s + <phi_j,s> z_j)/2 (j <= 3), y_4 = -s - (1/2) sum_j <phi_j,s> z_j, phi_0 = 0 (gauge); unknowns phi_1..phi_3 in V.
# Defect conditions (t^k coefficients in the parameters s_1..s_3, mu) -> Singular over Q(i).
import itertools, sympy as sp, numpy as np
I=sp.I
lines=[]
for p in itertools.permutations(range(4)):
    v=[ [1,I,-1,-I][k] for k in p ]
    if not any(abs(complex(sum(sp.conjugate(a)*b for a,b in zip(v,w))))>3.9 for w in lines): lines.append(v)
combo=(0,1,4,5); lam=[-1,1,I,-I]                               # first enumerated candidate, lambda scaled by 2
W=[[sp.expand(lam[j]*lines[combo[j]][r]) for j in range(4)] for r in range(4)]
assert all(sum(W[r][j] for j in range(4))==0 for r in range(4)), 'row sums'
assert all(sp.expand(sum(W[r][j]**2 for r in range(4)))==0 for j in range(4)), 'isotropy'
assert all(sum(W[r][j] for r in range(4))==0 for j in range(4)), 'column sums'
f=[[sp.Integer(0)]*4]+[list(sp.symbols('f%d_0:3'%k))+[None] for k in (1,2,3)]
for k in (1,2,3): f[k][3]=-(f[k][0]+f[k][1]+f[k][2])
s1,s2,s3,mu,t=sp.symbols('s1 s2 s3 mu t'); s=[s1,s2-s1,s3-s2,-s3]   # s in V
def pair(x,y): return sum(a*b for a,b in zip(x,y))
cols=[]
for j in range(4):
    c=pair(f[j],s); cols.append([ (s[r]+c*W[r][j])/2+mu*W[r][j] for r in range(4)])
cols.append([ -s[r]-sum(pair(f[j],s)*W[r][j] for j in range(4))/2 for r in range(4)])
Y=sp.Matrix(4,5,lambda r,c: cols[c][r])
C=[]
for j in range(5):
    M=sp.Matrix(4,4,lambda r,c: 1+t*Y[r,[x for x in range(5) if x!=j][c]]); C.append(sp.expand(M.per()))
eqs=set()
for D in (C[1]-C[0],C[2]-C[0],C[3]-C[0],C[4]+4*C[0]-120):
    for coeff in sp.Poly(sp.expand(D),t,s1,s2,s3,mu).coeffs():
        coeff=sp.expand(coeff)
        if coeff!=0: eqs.add(coeff)
vs=[x for k in (1,2,3) for x in f[k][:3]]
print('equations',len(eqs))
with open('/home/kevxhk/work/L-gct-210/stage3/r13/alpha0_W4.sing','w') as fh:
    fh.write('ring R=(0,I),(%s),dp;\nminpoly=I^2+1;\nideal J=%s;\nideal G=std(J);\n"ALPHA0 W4 RESULT size",size(G),"dim",dim(G);\nif(size(G)<=6){G;}\nquit;\n'%(','.join(map(str,vs)),',\n'.join(str(e).replace('**','^') for e in eqs)))
