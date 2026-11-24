# Round 13: case (beta) of [T31] split A for m0 in conic coordinates over Q (WLOG all t_j finite: the S_4-orbit of t = infinity has 6 points).
# z_j = l_j w(t_j); l_0 = 1; equations: moments, degree-3 (R_j) and degree-4 (P_j) line conditions, all l_j != 0.  Writes a Singular script.
# usage: python3 -I beta_t.py OUT.sing [extra]   extra: 'distinct' adds a Rabinowitsch for prod_{j<k}(t_j - t_k) != 0
import sys, itertools, sympy as sp
t=sp.symbols('t0:5'); l=[sp.Integer(1)]+list(sp.symbols('l1:5')); r=sp.Symbol('r'); q=sp.Symbol('q')
def esym(xs,k): return sum(sp.prod(c) for c in itertools.combinations(xs,k)) if k else sp.Integer(1)
def g(a,b,c): xs=[t[a],t[b],t[c]]; return esym(xs,1)+4*esym(xs,2)*esym(xs,3)
R=[]
for j in range(5):
    oth=[k for k in range(5) if k!=j]
    R.append(sp.expand(l[j]*sum(l[a]*l[b]*g(j,a,b) for a,b in itertools.combinations(oth,2))))
def h(idx):
    ts=[t[k] for k in idx]; ts2=[x**2 for x in ts]
    f=1+16*esym(ts,4)+16*esym(ts,4)**2+4*esym(ts2,2)-8*sum(ts2[m]*esym(ts[:m]+ts[m+1:],2) for m in range(4))
    a,b,c,d=ts; pair=(a-b)**2*(c-d)**2+(a-c)**2*(b-d)**2+(a-d)**2*(b-c)**2
    return 8*pair-3*f
P=[]
for j in range(5):
    oth=[k for k in range(5) if k!=j]; P.append(sp.expand(sp.prod([l[k] for k in oth])*h(oth)))
eqs=[sum(l), sum(l[j]*t[j] for j in range(5)), sum(l[j]*t[j]**2 for j in range(5)),
     R[1]-R[0], R[2]-R[0], R[3]-R[0], R[4]+4*R[0], P[1]-P[0], P[2]-P[0], P[3]-P[0], P[4]+4*P[0], r*l[1]*l[2]*l[3]-1]
vars_=list(t)+l[1:]+[r]
if len(sys.argv)>2 and sys.argv[2]=='distinct':
    eqs.append(q*sp.prod([t[a]-t[b] for a,b in itertools.combinations(range(5),2)])-1); vars_.append(q)
with open(sys.argv[1],'w') as fh:
    fh.write('ring R=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\n"BETA RESULT size",size(G),"dim",dim(G);\nif(size(G)<=3){G;}\nquit;\n'%(','.join(map(str,vars_)),',\n'.join(str(sp.expand(e)).replace('**','^') for e in eqs)))
print('written',sys.argv[1],'equations',len(eqs),'max total degree',max(sp.Poly(e,*vars_).total_degree() for e in eqs))
