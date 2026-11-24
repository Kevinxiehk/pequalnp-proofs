# verify2 r12: independent generators for rows R10.6 (EXT-II, EXT-I, CHI2). Differences from rows: constants in an algebraic extension
# (minpoly) instead of a variable; gauges on row 1 instead of row 0; permanents expanded in python (explicit S_4 sum) as polynomial strings.
import itertools
P4=list(itertools.permutations(range(4)))
def perm_str(Y,j):   # perm(J4 + Y^(j)) with Y a 4x5 matrix of strings
    cols=[c for c in range(5) if c!=j]
    return '+'.join('*'.join('(1+%s)'%Y[r][cols[p[r]]] for r in range(4)) for p in P4)
def write(fn,ring,Y,params,extra,post):
    L=[ring,'ideal E;']
    for j in range(5):
        L.append('poly F%d=%s-24;'%(j,perm_str(Y,j)))
    L+=extra
    L.append(post)
    open(fn,'w').write('\n'.join(L)+'\n')
# EXT-II: N_II = mu zeta (e0-e1)^T + mup zetabar (e2-e3)^T, zeta = (1,w,w^2,0), w primitive cube root (minpoly). Y modulo N_II, gauge Y[1][0] = Y[1][2] = 0
ys=['y%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==1 and j in (0,2))]
ze=['1','w','w^2','0']; zb=['1','w^2','w','0']
Y=[[None]*5 for _ in range(4)]
for i in range(4):
    for j in range(5):
        yv='yy*y%d%d'%(i,j) if not (i==1 and j in (0,2)) else '0'
        base={0:'mu*(%s)'%ze[i],1:'-mu*(%s)'%ze[i],2:'mup*(%s)'%zb[i],3:'-mup*(%s)'%zb[i],4:'0'}[j]
        Y[i][j]='(%s+%s)'%(base,yv)
write('ext2_mine.sing','ring R=(0,w),(mu,mup,yy,%s),dp; minpoly=w^2+w+1;'%','.join(ys),Y,None,
      ['int j; int k; matrix T; for(j=0;j<=4;j++){ execute("T=coef(F"+string(j)+",mu*mup*yy);"); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} }'],
      'ring R2=(0,w),(%s),dp; minpoly=w^2+w+1; option(redSB); ideal E=imap(R,E); ideal G=std(E); printf("EXT-II mine: dim %%s",dim(G)); print(radical(G)); quit;'%','.join(ys))
# EXT-I: N_I = chi (a e0 + b e1 - (a+b) e2)^T, chi = (1,i,-1,-i); Y modulo N_I, gauge Y[1][0] = Y[1][1] = 0
ys=['y%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==1 and j in (0,1))]
chi=['1','i','-1','-i']
for i in range(4):
    for j in range(5):
        yv='yy*y%d%d'%(i,j) if not (i==1 and j in (0,1)) else '0'
        base={0:'pa*(%s)'%chi[i],1:'pb*(%s)'%chi[i],2:'-(pa+pb)*(%s)'%chi[i],3:'0',4:'0'}[j]
        Y[i][j]='(%s+%s)'%(base,yv)
write('ext1_mine.sing','ring R=(0,i),(pa,pb,yy,%s),dp; minpoly=i^2+1;'%','.join(ys),Y,None,
      ['int j; int k; matrix T; for(j=0;j<=4;j++){ execute("T=coef(F"+string(j)+",pa*pb*yy);"); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} }'],
      'ring R2=(0,i),(%s),dp; minpoly=i^2+1; option(redSB); ideal E=imap(R,E); ideal G=std(E); printf("EXT-I mine: dim %%s",dim(G)); print(radical(G)); quit;'%','.join(ys))
# CHI2: L' = K_II + C Z, K_II = N_II + C w4 e4^T (w4 = (1,1,1,-3)); Z gauge Z[1][0] = Z[1][2] = Z[3][4] = 0 (w4_3 = -3 != 0);
# c(Z) = column sums = m; defect: F_j = m_j * F_0 ... rows used m_0 = 1; I use the PROJECTIVE form F_j * m_0 - m_j * F_0 = 0 with charts m_k = 1, k = 0..3.
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if not ((i==1 and j in (0,2)) or (i==3 and j==4))]
w4=['1','1','1','-3']
for i in range(4):
    for j in range(5):
        zv='t*z%d%d'%(i,j) if not ((i==1 and j in (0,2)) or (i==3 and j==4)) else '0'
        base={0:'mu*(%s)'%ze[i],1:'-mu*(%s)'%ze[i],2:'mup*(%s)'%zb[i],3:'-mup*(%s)'%zb[i],4:'y*(%s)'%w4[i]}[j]
        Y[i][j]='(%s+%s)'%(base,zv)
for ch in range(4):
    ms=['m%d'%k for k in range(5)]
    extra=['int j; int k; matrix T; poly cs; list mm=m0,m1,m2,m3,m4;',
           'for(j=0;j<=4;j++){ cs=0; for(k=0;k<=3;k++){ execute("cs=cs+subst(subst(subst(subst(F"+string(j)+",mu,0),mup,0),y,0),t,1);"); break; } }',
           ]
    # column sums of Z directly:
    colsum=['+'.join('z%d%d'%(i,j) if not ((i==1 and j in (0,2)) or (i==3 and j==4)) else '0' for i in range(4)) for j in range(5)]
    extra=['int j; int k; int l; matrix T; list mm=m0,m1,m2,m3,m4;']
    extra+=['E=E,(%s)-m%d;'%(colsum[j],j) for j in range(5)]
    extra+=['for(j=1;j<=4;j++){ execute("T=coef(m0*F"+string(j)+"-mm[j+1]*F0,mu*mup*y*t);"); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} }']
    extra+=['for(j=1;j<=4;j++){ for(k=j+1;k<=4;k++){ execute("T=coef(mm[j+1]*F"+string(k)+"-mm[k+1]*F"+string(j)+",mu*mup*y*t);"); for(l=1;l<=ncols(T);l++){E=E,T[2,l];} } }']
    extra+=['E=E,m%d-1;'%ch]
    write('chi2_mine_m%d.sing'%ch,'ring R=(0,w),(mu,mup,y,t,%s,m0,m1,m2,m3,m4),dp; minpoly=w^2+w+1;'%','.join(zs),Y,None,extra,
          'ring R2=(0,w),(%s,m0,m1,m2,m3,m4),dp; minpoly=w^2+w+1; option(redSB); ideal E=imap(R,E); ideal G=std(E); printf("CHI2 mine chart m%d=1: dim %%s vdim %%s",dim(G),vdim(G)); ideal Em=eliminate(G,%s); print(std(Em)); quit;'%(','.join(zs),ch,'*'.join(zs)))
print('written')
