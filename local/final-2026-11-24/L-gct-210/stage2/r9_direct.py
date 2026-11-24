# DIRECT (FO-r) incidence system, independent of all cofactor formulas and of [CRIT]:
#   X = span of 5 basis 4x5 matrices B_1..B_5 (entries polynomials in parameters), placed in rows 1..4 of a 5x5 matrix (row 0 = 0);
#   U = J + sum_k z_k B_k ; C_ij = perm(U without row i, column j) (computed by explicit 24-term expansion).
#   (0, e_m) in Omega  <=>  exists t in C^{4x5}:  C_0m + sum_{i>=1, j} t_ij C_ij = 0 identically in z.
#   Omega = C^5 <=> (0,e_1),(0,e_2),(0,e_3) in Omega  (e_0 and 1 are always in Omega, NOTES R7-1).
# Also emits LEVEL checks: perm(U) - 120 and the five 4x4 column-deletion permanents of rows 1..4 must vanish identically
# (modulo the parameter ideal), printed as "LEVEL CHECK".
# usage: r9_direct.py FAMILY CHAR VLIST   -> Singular script on stdout
import sys, itertools
fam=sys.argv[1]; ch=sys.argv[2]; vl=[int(c) for c in sys.argv[3]]
P4=list(itertools.permutations(range(4)))
def zero(): return [['0']*5 for _ in range(4)]
eqpar=[]
if fam=='FM':      # B(ind) pattern M (validation of R9-1 by an independent route); Y_0 coords (zeta1, zeta2, a, b) = basis vectors
    par=['al','be','ga','de','mu']; eqpar=['ga*(4*al-1)','be*(4*de-1)','1-de-al+4*(al*de+be*ga)']
    def pq(x):  # x = (x1,x2,x3,x4) numeric unit vector -> strings
        x1,x2,x3,x4=x; pi='(al*%d+be*%d)'%(x3,x4); ka='(ga*%d+de*%d)'%(x3,x4); sg='(%d-2*%s)'%(x3,pi); ta='(%d-2*%s)'%(x4,ka)
        return ['(%s/2+%d)'%(sg,x1),'(%s/2-%d)'%(sg,x1),pi,pi],[ka,ka,'(%s/2+%d)'%(ta,x2),'(%s/2-%d)'%(ta,x2)]
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
    for k in range(4):
        x=[0,0,0,0]; x[k]=1; p,q=pq(x); a='(%s)'%'+'.join(p); b='(%s)'%'+'.join(q)
        s='((1-mu)*%s+(1+mu)*%s)'%(a,b); M=zero(); M[0][0]='(%s/2)'%s; M[1][0]='(%s/2)'%s
        M[2][0]='(-%s-(1+mu)*%s)'%(a,b); M[3][0]='((mu-1)*%s-%s)'%(a,b)
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
elif fam=='D1M':   # B(dep): b = lam*a, Y_00 of pattern M; covers lam != 0 completely and the M-part of lam = 0, dim Y = 3
    par=['al','ga','lam']; eqpar=['lam*(1-al)-ga*(1-4*al)']
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)                                  # xi_d
    M=zero(); M[0][0]='((lam-1)/2)'; M[1][0]='((lam-1)/2)'; M[2][0]='(-lam)'; M[3][0]='1'; B.append(M)   # kappa_1 (q0 = 1)
    for (z1,z2,aa) in [(1,0,0),(0,1,0),(0,0,1)]:
        sg='((1-2*al)*%d)'%aa; ta='((lam-2*ga)*%d)'%aa
        p=['(%s/2+%d)'%(sg,z1),'(%s/2-%d)'%(sg,z1),'(al*%d)'%aa,'(al*%d)'%aa]
        q=['(ga*%d)'%aa,'(ga*%d)'%aa,'(%s/2+%d)'%(ta,z2),'(%s/2-%d)'%(ta,z2)]
        M=zero(); M[0][0]='(lam*(1+lam)*%d/2)'%aa; M[1][0]='(lam*(1+lam)*%d/2)'%aa; M[2][0]='(-(1+lam)^2*%d)'%aa; M[3][0]='0'
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
elif fam=='D0Q':   # B(dep), lam = 0 (b = 0 on X), dim Y = 3, pattern Q0: A' = n^perp (chart n4 = 1), q' = ca * a * w, w = n - (sum n/4) 1
    par=['n1','n2','n3','ca']; eqpar=['ca*(n1+n2+n3+1)']
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
    M=zero(); M[0][0]='(-1/2)'; M[1][0]='(-1/2)'; M[3][0]='1'; B.append(M)                  # kappa (q0 = 1, s = -1, p0 = 0)
    nn=['n1','n2','n3','1']; sn='(n1+n2+n3+1)'
    for k in range(3):
        x=[0,0,0]; x[k]=1
        p=[str(x[0]),str(x[1]),str(x[2]),'(-n1*%d-n2*%d-n3*%d)'%tuple(x)]; a='(%s)'%'+'.join(p)
        q=['(ca*%s*(%s-%s/4))'%(a,nn[j],sn) for j in range(4)]
        M=zero(); M[2][0]='(-%s)'%a
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
elif fam=='D0P':   # B(dep), lam = 0, dim Y = 3, pattern P0: q'(Y) = V' = rowspace[[1,0,r1,-1-r1],[0,1,r2,-1-r2]], p' = a*P, P in V'^perp, sum P = 1
    par=['r1','r2','P3','P4']; Pv=['(-r1*P3+(1+r1)*P4)','(-r2*P3+(1+r2)*P4)','P3','P4']; eqpar=['(%s)-1'%'+'.join(Pv)]
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
    M=zero(); M[0][0]='(-1/2)'; M[1][0]='(-1/2)'; M[3][0]='1'; B.append(M)
    V=[['1','0','r1','(-1-r1)'],['0','1','r2','(-1-r2)']]
    for k in range(3):
        M=zero()
        if k<2:
            for j in range(4): M[3][j+1]=V[k][j]
        else:
            M[2][0]='(-1)'
            for j in range(4): M[2][j+1]=Pv[j]
        B.append(M)
elif fam in ('D00Q','D00P','D00M'):   # B(dep), a = b = 0, dim Y = 2: X = column-0 space {s1+s2+p0+q0 = 0} (+) Y (zero column 0); N0 on Y
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
    M=zero(); M[0][0]='(-1/2)'; M[1][0]='(-1/2)'; M[2][0]='1'; B.append(M)
    M=zero(); M[0][0]='(-1/2)'; M[1][0]='(-1/2)'; M[3][0]='1'; B.append(M)
    if fam=='D00M':
        par=[]; Ys=[(['1','-1','0','0'],['0']*4),(['0']*4,['0','0','1','-1'])]
    else:
        par=['r1','r2']; V=[['1','0','r1','(-1-r1)'],['0','1','r2','(-1-r2)']]
        Ys=[(V[k],['0']*4) for k in range(2)] if fam=='D00Q' else [(['0']*4,V[k]) for k in range(2)]
    for (p,q) in Ys:
        M=zero()
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
elif fam.startswith('D04_'):   # B(dep), lam = 0 (b = 0), dim Y = 4: Y = C(1',0) + W + C y3, W = pattern (N0-W), Y_a = W + C y3 maximal isotropic
    _,pat,cho,case=fam.split('_')
    if pat in ('Q0','P0'):
        par=['r1','r2']; V=[['1','0','r1','(-1-r1)'],['0','1','r2','(-1-r2)']]
        w=['(-r1*(3+r1+r2)+(1+r1)*(r1+r2-1))','(-r2*(3+r1+r2)+(1+r2)*(r1+r2-1))','(3+r1+r2)','(r1+r2-1)']
        Z4=['0']*4; e34=['0','0','1','-1']
        if pat=='Q0': Wb=[(V[0],Z4),(V[1],Z4)]; y3=(e34,Z4) if cho=='A' else (Z4,w)
        else:         Wb=[(Z4,V[0]),(Z4,V[1])]; y3=(Z4,e34) if cho=='A' else (w,Z4)
    else:
        par=[]; Z4=['0']*4; Wb=[(['1','-1','0','0'],Z4),(Z4,['0','0','1','-1'])]
        y3=(['-1','-1','1','1'],Z4) if cho=='A' else (Z4,['1','1','-1','-1'])
    Yb=[(['1']*4,['0']*4)]+Wb+[y3]          # a = 4 on h, 0 on W and y3
    B=[]
    if case=='i':                            # xi_d in X; phi(h) = f0, phi = 0 on W, phi(y3) = f3; col0 = (-phi/2,-phi/2,-a,phi)
        par+=['f0','f3']; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
        ph=['f0','0','0','f3']; aa=['4','0','0','0']
        for k,(p,q) in enumerate(Yb):
            M=zero(); M[0][0]='(-%s/2)'%ph[k]; M[1][0]='(-%s/2)'%ph[k]; M[2][0]='(-%s)'%aa[k]; M[3][0]=ph[k]
            for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
            B.append(M)
    else:                                    # kappa' = (sg,-1-sg,0,1); lift q0 = 0, s1 = d, s2 = -d, d(h) = d0, d = 0 on W, d(y3) = d3
        par+=['sg','d0','d3']; M=zero(); M[0][0]='sg'; M[1][0]='(-1-sg)'; M[3][0]='1'; B.append(M)
        dd=['d0','0','0','d3']; aa=['4','0','0','0']
        for k,(p,q) in enumerate(Yb):
            M=zero(); M[0][0]=dd[k]; M[1][0]='(-%s)'%dd[k]; M[2][0]='(-%s)'%aa[k]; M[3][0]='0'
            for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
            B.append(M)
elif fam in ('FP0d','FQ0d'):   # B(ind) families FP0 (mu = 1) and FQ0 (mu = -1) for the DIRECT tool (independent check of R9-1)
    B=[]; M=zero(); M[0][0]='1'; M[1][0]='-1'; B.append(M)
    if fam=='FP0d':
        par=['al2','al3','al4']; mu='1'
        ns=[['-al2','1','0','0'],['-al3','0','1','0'],['-al4','0','0','1']]
        Ys=[(['1','al2','al3','al4'],['0']*4)]
        for n in ns:
            sn='(%s)'%'+'.join('(%s)'%t for t in n); Ys.append((['0']*4,['(%s-3*(%s))'%(sn,t) for t in n]))
    else:
        par=['n1','n2','n3']; mu='-1'; nn=['n1','n2','n3','1']; sn='(n1+n2+n3+1)'
        Ys=[]
        for k in range(3):
            x=[0,0,0]; x[k]=1; Ys.append(([str(x[0]),str(x[1]),str(x[2]),'(-n1*%d-n2*%d-n3*%d)'%tuple(x)],['0']*4))
        Ys.append((['0']*4,['(%s-3*%s)'%(sn,t) for t in nn]))
    for (p,q) in Ys:
        a='(%s)'%'+'.join(p); b='(%s)'%'+'.join(q); s='((1-(%s))*%s+(1+(%s))*%s)'%(mu,a,mu,b)
        M=zero(); M[0][0]='(%s/2)'%s; M[1][0]='(%s/2)'%s; M[2][0]='(-%s-(1+(%s))*%s)'%(a,mu,b); M[3][0]='(((%s)-1)*%s-%s)'%(mu,a,b)
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
elif fam.startswith('D003_'):   # B(dep), a = b = 0, dim Y = 3 (Y max isotropic in 1^perp x 1^perp), NON-PROP (N0-W):
    # X = K2 (+) lift(W) (+) C lift(y3);  K2 = {x in C3 : k.x = 0} (C3 = column-0 space, basis c1 = xi_d, c2 = (-1/2,-1/2,1,0), c3 = (-1/2,-1/2,0,1));
    # chart CH in {3,2,1}: k = (k1,k2,1), (k1,1,0), (1,0,0);  lift(W) has zero column 0; lift(y3) has column 0 = u3 (3 free coordinates in C3).
    _,pat,cho,ch_=fam.split('_')
    Z4=['0']*4
    if pat in ('Q0','P0'):
        par=['r1','r2']; V=[['1','0','r1','(-1-r1)'],['0','1','r2','(-1-r2)']]
        w=['(-r1*(3+r1+r2)+(1+r1)*(r1+r2-1))','(-r2*(3+r1+r2)+(1+r2)*(r1+r2-1))','(3+r1+r2)','(r1+r2-1)']
        e34=['0','0','1','-1']
        if pat=='Q0': Wb=[(V[0],Z4),(V[1],Z4)]; y3=(e34,Z4) if cho=='A' else (Z4,w)
        else:         Wb=[(Z4,V[0]),(Z4,V[1])]; y3=(Z4,e34) if cho=='A' else (w,Z4)
    else:
        par=[]; Wb=[(['1','-1','0','0'],Z4),(Z4,['0','0','1','-1'])]
        y3=(['-1','-1','1','1'],Z4) if cho=='A' else (Z4,['1','1','-1','-1'])
    cvec=[['1','-1','0','0'],['(-1/2)','(-1/2)','1','0'],['(-1/2)','(-1/2)','0','1']]
    if ch_=='3': par+=['k1','k2']; Kb=[['1','0','(-k1)'],['0','1','(-k2)']]
    elif ch_=='2': par+=['k1']; Kb=[['1','(-k1)','0'],['0','0','1']]
    else: Kb=[['0','1','0'],['0','0','1']]
    par+=['u1']; comp={'3':2,'2':1,'1':0}[ch_]      # column 0 of lift(y3) = u1 * (complement of K2 in C3); K2 itself is in X
    B=[]
    for kb in Kb:
        M=zero()
        for r in range(4): M[r][0]='(%s)'%'+'.join('(%s)*(%s)'%(kb[i],cvec[i][r]) for i in range(3))
        B.append(M)
    for (p,q) in Wb:
        M=zero()
        for j in range(4): M[2][j+1]=p[j]; M[3][j+1]=q[j]
        B.append(M)
    M=zero()
    for r in range(4): M[r][0]='(u1*(%s))'%cvec[comp][r]
    for j in range(4): M[2][j+1]=y3[0][j]; M[3][j+1]=y3[1][j]
    B.append(M)
else:
    raise SystemExit('unknown family')
nz=len(B); zs=['z%d'%(k+1) for k in range(nz)]
unk=[]
for i,m in enumerate(vl,1): unk+=['t%d_%d%d'%(i,a,b) for a in range(1,5) for b in range(5)]
print('ring R=%s,(%s),dp;'%(ch,','.join(unk+par+zs)))
print('option(redSB);')
print('ideal PI=%s; ideal PS=std(PI);'%(','.join(eqpar) if eqpar else '0'))
print('matrix U[5][5];')
for i in range(5):
    for j in range(5):
        if i==0: print('U[1,%d]=1;'%(j+1))
        else: print('U[%d,%d]=1+%s;'%(i+1,j+1,'+'.join('%s*(%s)'%(zs[k],B[k][i-1][j]) for k in range(nz))))
def permexpr(rows,cols): return '+'.join('*'.join('U[%d,%d]'%(rows[r]+1,cols[pp[r]]+1) for r in range(4)) for pp in P4)
print('matrix CF[5][5];')
for i in range(5):
    for j in range(5):
        rows=[r for r in range(5) if r!=i]; cols=[c for c in range(5) if c!=j]
        print('CF[%d,%d]=%s;'%(i+1,j+1,permexpr(rows,cols)))
# level check: perm(U) = sum_j U[1][j] CF[1][j] (row-0 expansion) ; G_j = perm of rows 1..4 of xi without column j
print('poly PU=0; int jj; for(jj=1;jj<=5;jj++){PU=PU+U[1,jj]*CF[1,jj];}')
print('matrix C; int k; ideal LV; poly F;')
print('F=PU-120; C=coef(F,%s); for(k=1;k<=ncols(C);k++){LV=LV+ideal(C[2,k]);}'%('*'.join(zs)))
print('"LEVEL CHECK perm(J+xi)=120 (must be 1):", size(reduce(LV,PS))==0;')
print('ideal I=PI;')
for i,m in enumerate(vl,1):
    F='CF[1,%d]+'%(m+1)+'+'.join('t%d_%d%d*CF[%d,%d]'%(i,a,b,a+1,b+1) for a in range(1,5) for b in range(5))
    print('F=%s; C=coef(F,%s); for(k=1;k<=ncols(C);k++){I=I+ideal(C[2,k]);}'%(F,'*'.join(zs)))
print('int t=timer; ideal G=std(I); "RESULT direct %s char %s v=%s: size(std)=",size(G),", unit:",(reduce(1,G)==0), ", dim=",dim(G),", sec=",timer-t;'%(fam,ch,''.join(map(str,vl))))
print('if(size(G)<=30){G;}')
print('quit;')
