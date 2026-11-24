# exact certificates (sympy over Q) at the points left over by gen_rank.py (TASK X1', NOTES-reg2 section 11)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp, itertools
def perm(M):
    n=M.shape[0]
    return sp.Add(*[sp.Mul(*[M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))])
def T1_exact(B):
    ys=sp.symbols('y1:%d'%(len(B)+1)); A=sp.ones(5,5)
    for k,b in enumerate(B): A[:4,:]+=ys[k]*b
    lev=sp.expand(sum(perm(A[:4,[c for c in range(5) if c!=j]]) for j in range(5))-120)==0
    rows={}
    for i in range(5):
        for j in range(5):
            m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
            for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
    Am=sp.Matrix(list(rows.values())); return lev,25-Am.rank()
def rowel(i,w): m=sp.zeros(4,5); m[i,:]=sp.Matrix([w]); return m
def colel(c,x): m=sp.zeros(4,5); m[:,c]=sp.Matrix(x); return m
def sp213(u):
    u=[sp.Rational(x) for x in u]+[0]
    H=sp.Matrix([[1,1,1,1,1],[0,0,0,0,1],u]).nullspace()
    return [rowel(0,list(h)) for h in H]+[rowel(1,u)]+[colel(4,[1,-1,0,0]),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])]
def sp321a(xp):
    x2=[0,xp[2]-xp[3],xp[3]-xp[1],xp[1]-xp[2]]
    return [rowel(0,[1 if j==0 else (-1 if j==k else 0) for j in range(5)]) for k in (1,2,3)]+[colel(4,[3,-1,-1,-1]),colel(4,x2),colel(3,xp)]
which=sys.argv[1]
if which=='213':
    pts=[(1,-1,1,-1),(1,-3,1,1),(1,1,1,-3),(1,1,-3,1),(3,-1,-1,-1),(1,-1,0,0),(2,-1,0,-1),(1,0,0,-1),(1,0,-1,0),(1,1,-1,-1),(1,-1,-1,1)]
    for u in pts:
        lev,n=T1_exact(sp213(u)); print('(2,1|3) u=%s: level %s, dim T_1 = %d'%(u,lev,n),flush=True)
elif which=='321':
    lev,n=T1_exact(sp321a([0,0,1,-1])); print('(3|2,1)(a) x=(0,0,1,-1): level %s, dim T_1 = %d'%(lev,n),flush=True)
    B=[rowel(0,[1 if j==0 else (-1 if j==k else 0) for j in range(5)]) for k in (1,2,4)]+[colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1]),colel(3,[-3,1,1,1])]
    lev,n=T1_exact(B); print('(3|2,1)(b2): level %s, dim T_1 = %d'%(lev,n),flush=True)
elif which=='3111':
    U=[rowel(0,[1 if j==0 else (-1 if j==k else 0) for j in range(5)]) for k in (1,2,3)]
    x2=[0,0,1,-1]; x3=[0,x2[2]-x2[3],x2[3]-x2[1],x2[1]-x2[2]]
    lev,n=T1_exact(U+[colel(4,[3,-1,-1,-1]),colel(2,x2),colel(3,x3)]); print('(3|1,1,1)(b-i) x2=(0,0,1,-1): level %s, dim T_1 = %d'%(lev,n),flush=True)
    w=sp.Rational(-1,2)+sp.sqrt(-3)/2; l=[0,1,w,sp.expand(w**2)]
    B=U+[colel(4,[3,-1,-1,-1]),colel(2,l),colel(3,l)]
    ys=sp.symbols('y1:7'); A=sp.ones(5,5)
    for k,b in enumerate(B): A[:4,:]+=ys[k]*b
    lev=sp.expand(sum(perm(A[:4,[c for c in range(5) if c!=j]]) for j in range(5))-120)==0
    rows={}
    for i in range(5):
        for j in range(5):
            m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
            for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
    K=sp.QQ.algebraic_field(sp.sqrt(-3)); rk=sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(list(rows.values()))).convert_to(K).rank()
    print('(3|1,1,1)(b-ii) l=(0,1,w,w^2): level %s, dim T_1 = %d'%(lev,25-rk),flush=True)
elif which=='2121':
    def T1_alg(B):
        ys=sp.symbols('y1:%d'%(len(B)+1)); A=sp.ones(5,5)
        for k,b in enumerate(B): A[:4,:]+=ys[k]*b
        lev=sp.expand(sum(perm(A[:4,[c for c in range(5) if c!=j]]) for j in range(5))-120)==0
        rows={}
        for i in range(5):
            for j in range(5):
                m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
                for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
        K=sp.QQ.algebraic_field(sp.sqrt(-3))
        return lev,25-sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(list(rows.values()))).convert_to(K).rank()
    def U0(u,zero_cols):
        M=sp.Matrix([[1]*5,list(u)]+[[1 if j==k else 0 for j in range(5)] for k in zero_cols]); return [list(v) for v in M.nullspace()]
    def x2of(xp): return [0,xp[2]-xp[3],xp[3]-xp[1],xp[1]-xp[2]]
    for (a,b) in [(-3,1),(1,1),(-1,1),(sp.Rational(-1,2),sp.Rational(-1,2)),(0,0),(sp.Rational(-1,3),sp.Rational(-1,3)),(1,-3),(0,-1),(1,-1),(-1,-1)]:
        u=[1,a,b,-1-a-b,0]
        B=[rowel(0,h) for h in U0(u,[4])]+[rowel(1,u),colel(4,[1,-1,0,0]),colel(4,[1,1,-1,-1]),colel(3,[0,0,1,-1])]
        lev,n=T1_alg(B); print('(2,1|2,1)Vn-i u=%s: level %s, dim T_1 = %d'%(u,lev,n),flush=True)
    w=sp.Rational(-1,2)+sp.sqrt(-3)/2; h=sp.Rational(1,2)
    for (s_,p) in [(-1,-h),(-1,w),(-1,-1),(-1,0),(-h,-h),(-2,-h),(1,-h),(1,-1),(1,0),(-h,0)]:
        u=[1,s_,-1-s_,0,0]; xp=[0,1,p,sp.expand(-1-p)]
        B=[rowel(0,hh) for hh in U0(u,[4])]+[rowel(1,u),colel(4,[3,-1,-1,-1]),colel(4,[sp.expand(e) for e in x2of(xp)]),colel(3,xp)]
        lev,n=T1_alg(B); print('(2,1|2,1)Vn-ii s=%s p=%s: level %s, dim T_1 = %d'%(s_,p,lev,n),flush=True)
elif which=='11121':
    def T1_alg(B):
        ys=sp.symbols('y1:%d'%(len(B)+1)); A=sp.ones(5,5)
        for k,b in enumerate(B): A[:4,:]+=ys[k]*b
        lev=sp.expand(sum(perm(A[:4,[c for c in range(5) if c!=j]]) for j in range(5))-120)==0
        rows={}
        for i in range(5):
            for j in range(5):
                m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
                for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
        K=sp.QQ.algebraic_field(sp.sqrt(-3))
        return lev,25-sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(list(rows.values()))).convert_to(K).rank()
    c3=lambda u:[u[1]-u[2],u[2]-u[0],u[0]-u[1],0,0]
    x2of=lambda xp:[0,xp[2]-xp[3],xp[3]-xp[1],xp[1]-xp[2]]
    w=sp.Rational(-1,2)+sp.sqrt(-3)/2; h=sp.Rational(1,2)
    for (s_,p) in ([] if 'new' in sys.argv else [(0,-1),(-h,-1),(w,-1),(-2,-h),(w,0)]):
        u=[1,s_,sp.expand(-1-s_),0,0]; xp=[0,1,p,-1-p]
        B=[rowel(0,[1,1,1,-3,0]),rowel(1,u),rowel(2,[sp.expand(e) for e in c3(u)]),colel(4,[3,-1,-1,-1]),colel(4,x2of(xp)),colel(3,xp)]
        lev,n=T1_alg(B); print('(1,1,1|2,1)B1 s=%s p=%s: level %s, dim T_1 = %d'%(s_,p,lev,n),flush=True)
    for (s_,q) in ([(-1,4),(-1,1),(-1,-h),(-1,-2)] if 'new' in sys.argv else [(-2,0),(-h,0),(0,0),(1,0),(-1,0),(0,-4),(0,h),(0,2)]):
        u2=[1,s_,-1-s_,0,0]; g1=[1,1,1,-3,0]; g2=c3(u2); u0=[g1[j]+q*g2[j] for j in range(5)]
        a=sum(x*y for x,y in zip(u0,g2)); b=sum(x*y for x,y in zip(u0,g1)); u1=[a*g1[j]-b*g2[j] for j in range(5)]
        B=[rowel(0,u0),rowel(1,u1),rowel(2,u2),colel(4,[1,-1,0,0]),colel(4,[1,1,-1,-1]),colel(3,[0,0,1,-1])]
        lev,n=T1_alg(B); print('(1,1,1|2,1)B2 s=%s q=%s: level %s, dim T_1 = %d'%(s_,q,lev,n),flush=True)
elif which=='1111pt':
    # (1,1,1,1|2) case A, |N| = 0: u_0 = (1,1,1,1,-4), u_1 = u_2 = u_3 = (1,i,-1,-i,0), V = {x_0 = 0, sum = 0} in column 4
    I_=sp.I; l=[1,I_,-1,-I_,0]
    B=[rowel(0,[1,1,1,1,-4]),rowel(1,l),rowel(2,l),rowel(3,l),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1])]
    ys=sp.symbols('y1:7'); A=sp.ones(5,5)
    for k,b in enumerate(B): A[:4,:]+=ys[k]*b
    lev=sp.expand(sum(perm(A[:4,[c for c in range(5) if c!=j]]) for j in range(5))-120)
    print('(1,1,1,1|2) point (g, chi_1 x3): level identity', lev==0, '' if lev==0 else str(sp.factor(lev))[:200],flush=True)
    if lev==0:
        rows={}
        for i in range(5):
            for j in range(5):
                m=A.copy(); m.row_del(i); m.col_del(j); P=sp.Poly(sp.expand(perm(m)),*ys)
                for mon,cf in P.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
        K=sp.QQ.algebraic_field(sp.I); print('dim T_1 =',25-sp.polys.matrices.DomainMatrix.from_Matrix(sp.Matrix(list(rows.values()))).convert_to(K).rank())
elif which=='21111':
    lev,n=T1_exact([rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,0,0,-1]),rowel(1,[1,1,0,-3,1]),colel(2,[1,-3,1,1]),colel(3,[2,0,-1,-1]),colel(4,[0,0,1,-1])])
    print('(2,1|1,1,1)ABD: level %s, dim T_1 = %d'%(lev,n),flush=True)
    x2=[0,0,1,-1]; x3=[0,x2[2]-x2[3],x2[3]-x2[1],x2[1]-x2[2]]
    lev,n=T1_exact([rowel(0,[1,1,0,-1,-1]),rowel(0,[0,0,0,1,-1]),rowel(1,[1,-1,0,0,0]),colel(2,[3,-1,-1,-1]),colel(3,x2),colel(4,x3)])
    print('(2,1|1,1,1)ACC x2=(0,0,1,-1): level %s, dim T_1 = %d'%(lev,n),flush=True)
    u=[1,-1,0,0,0]; W=sp.Matrix([[1,1,1,1,1],[0,0,1,0,0],u]).nullspace()
    lev,n=T1_exact([rowel(0,list(w)) for w in W]+[rowel(1,u),colel(2,[3,-1,-1,-1]),colel(3,[0,2,-1,-1]),colel(4,[0,0,1,-1])])
    print('(2,1|1,1,1)ACD s=-1: level %s, dim T_1 = %d'%(lev,n),flush=True)
