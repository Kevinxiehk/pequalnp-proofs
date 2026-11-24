# verify2 r10: INDEPENDENT exact check of rows R8.9 (PL4 for sign patterns ++++ / ----), own formulation (Singular over Q):
# B_j = R B0_j R^T, R^T R = I (all of O(3,C)), A_j = (1 - B_j)/2; columns y_j(tau) = H A_j tau (Walsh -> C^4), tau in C^3 (Walsh coordinates of V);
# conditions: tau(y_a o y_b o y_c) == 0 for the four triples of active columns (all tau-coefficients). r^2 = 5 (++++) / r^2 = -3, ii^2 = -1 (----).
# CAL: the 3-column (1,1,1) configuration A_j = projectors onto the Walsh axes (must be NON-unit).   usage: python3 -I orb_indep.py OUTDIR
import sys, itertools, sympy as sp
out=sys.argv[1]
R=sp.Matrix(3,3,sp.symbols('R0:9')); r=sp.Symbol('r'); ii=sp.Symbol('ii'); tau=sp.Matrix(sp.symbols('u0:3'))
H=sp.Matrix([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]])
hs=[H[j,:].T for j in range(4)]
def cross(h): return sp.Matrix([[0,-h[2],h[1]],[h[2],0,-h[0]],[-h[1],h[0],0]])
I3=sp.eye(3)
confs={'pppp':[I3/4+h*h.T/4+r/4*cross(h) for h in hs], 'mmmm':[sp.Rational(5,4)*I3-sp.Rational(3,4)*h*h.T-ii*r/4*cross(h) for h in hs]}
extra={'pppp':['r^2-5'],'mmmm':['r^2-3','ii^2+1']}
cal=[I3-2*sp.Matrix([[1 if (a==j and b==j) else 0 for b in range(3)] for a in range(3)]) for j in range(3)]   # B = 1 - 2 P_axis_j
for name,B0 in list(confs.items())+[('cal3',cal)]:
    A=[(I3-R*b*R.T)/2 for b in B0]
    cols=[H*(a*tau) for a in A]
    eqs=set()
    for T in itertools.combinations(range(len(cols)),3):
        f=sp.expand(sum(cols[T[0]][k]*cols[T[1]][k]*cols[T[2]][k] for k in range(4)))
        for c in sp.Poly(f,*tau).coeffs(): eqs.add(sp.expand(c))
    orth=[sp.expand(e) for e in (R.T*R-I3) if sp.expand(e)!=0]
    allv=list(R)+([r] if name!='cal3' else [])+([ii] if name=='mmmm' else [])
    def s(e): return str(e).replace('**','^')
    ex=extra.get(name,[])
    open('%s/orb_%s.sing'%(out,name),'w').write('ring rr=0,(%s),dp;\nideal I=%s;\nideal G=std(I);\nif (size(G)==1 and G[1]==1) {"RES %s UNIT";} else {"RES %s NONUNIT dim",dim(G);}\nquit;\n'%(','.join(map(str,allv)),',\n'.join([s(e) for e in eqs]+[s(e) for e in orth]+ex),name,name))
    print(name,'equations',len(eqs),flush=True)
