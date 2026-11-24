# the 60 known K' points (exact, mod p): K' = span{(e_p - e_q, 0), (0, e_s1), (0, e_s2)} and its a<->b mirror; m = e_p - e_q.
# For a chart (pivots S, m-chart J): list the known points inside, check that every equation of the chart system vanishes there
# (calibration) and compute the Jacobian rank mod p (= number of unknowns  <=>  local length 1).
import sys, itertools, sympy as sp
P=int(sys.argv[1]); S=[int(c) for c in sys.argv[2].split(',')]; J=int(sys.argv[3]); msf=sys.argv[4]
L=open(msf).read().split('\n'); vars_=L[0].strip().split(','); eqs_txt=[e for e in ''.join(L[2:]).split(',') if e.strip()]
syms=sp.symbols(vars_); env=dict(zip(vars_,syms))
eqs=[sp.Poly(sp.sympify(e.replace('^','**'),locals=env),*syms,modulus=P) for e in eqs_txt]
jac=[[e.diff(x) for x in syms] for e in eqs]
pts=[]
for p,q in itertools.combinations(range(5),2):
    rest=[j for j in range(5) if j not in (p,q)]
    for s1,s2 in itertools.combinations(rest,2):
        for mir in (0,1):
            a=[0]*10; a[(5 if mir else 0)+p]=1; a[(5 if mir else 0)+q]=P-1
            b1=[0]*10; b1[(0 if mir else 5)+s1]=1
            b2=[0]*10; b2[(0 if mir else 5)+s2]=1
            m=[0]*5; m[p]=1; m[q]=P-1
            pts.append(((p,q,s1,s2,mir),[a,b1,b2],m))
def inv(x): return pow(x%P,P-2,P)
found=0; bad=0; ranks=[]
for tag,Bm,m in pts:
    M=sp.Matrix(Bm); sub=M[:,S]
    if sub.det()%P==0 or m[J]%P==0: continue
    G=(sub.inv_mod(P)*M).applyfunc(lambda x: x%P)
    val={}
    free=[c for c in range(10) if c not in S]
    for s in range(3):
        for c in free: val['g%d_%d'%(s,c)]=int(G[s,c])
    mj=inv(m[J])
    for j in range(5):
        if j!=J: val['M%d'%j]=m[j]*mj%P
    pt=[val[v] for v in vars_]
    nz=sum(1 for e in eqs if e.eval(dict(zip(syms,pt)))%P!=0 if True) if False else sum(1 for e in eqs if int(e.eval(tuple(pt)) if len(syms)>1 else e.eval(pt[0]))%P!=0)
    Jm=sp.Matrix([[int(d.eval(tuple(pt)))%P for d in row] for row in jac])
    r=Jm.rank(iszerofunc=lambda x: x%P==0) if False else None
    # rank mod p via row reduction
    A=[[int(x)%P for x in row] for row in Jm.tolist()]; rk=0; ncol=len(vars_)
    for c in range(ncol):
        pr=next((i for i in range(rk,len(A)) if A[i][c]%P),None)
        if pr is None: continue
        A[rk],A[pr]=A[pr],A[rk]; iv=inv(A[rk][c]); A[rk]=[x*iv%P for x in A[rk]]
        for i in range(len(A)):
            if i!=rk and A[i][c]%P:
                f=A[i][c]; A[i]=[(x-f*y)%P for x,y in zip(A[i],A[rk])]
        rk+=1
    found+=1; bad+=(nz>0); ranks.append(rk)
    print(tag,'nonvanishing eqs',nz,'jacobian rank',rk,'of',ncol)
print('chart',S,'J',J,': known points inside',found,' failing',bad,' all reduced' if all(r==len(vars_) for r in ranks) else ' NOT all reduced')
