# verify2 r15: independent check of stage3 SR5's configuration (3,2): rows 0,1,2 carry m, rows 3,4 carry m' (m' not parallel to m): the span
# {sum_{i<3} c_i e_i m^T + sum_{i>=3} c_i e_i m'^T} is level  <=>  perm(J + Y) = 120 identically in c.  Direct permanent expansion (S_5), all
# c-coefficients.  m, m' in C^5 (sum zero by P_1, imposed automatically by the equations).  Charts: m_k = 1 (k = 0..4) x (m' not parallel to m):
# u * (m_k m'_j - m_j m'_k) = 1 for j != k (covers m' not in C m).  Calibrations: (2,2), (3,1), (2,1) row distributions.
import sys, itertools
A,B=int(sys.argv[1]),int(sys.argv[2]); k=int(sys.argv[3]); j=int(sys.argv[4])
rows=['m']*A+['n']*B+['0']*(5-A-B)
P5=list(itertools.permutations(range(5)))
cs=['c%d'%i for i in range(A+B)]
L=['ring R=0,(m0,m1,m2,m3,m4,n0,n1,n2,n3,n4,u,%s),dp;'%','.join(cs),'matrix Y[5][5];']
for i in range(5):
    for col in range(5):
        if rows[i]=='0': L.append('Y[%d,%d]=1;'%(i+1,col+1))
        else: L.append('Y[%d,%d]=1+c%d*%s%d;'%(i+1,col+1,i,rows[i],col))
L.append('poly F=%s-120;'%'+'.join('*'.join('Y[%d,%d]'%(r+1,p[r]+1) for r in range(5)) for p in P5))
L.append('matrix M=coef(F,%s); ideal E; int t; for(t=1;t<=ncols(M);t++){E=E,M[2,t];}'%'*'.join(cs))
L.append('E=E,m%d-1,u*(m%d*n%d-m%d*n%d)-1;'%(k,k,j,j,k))
L.append('ring R2=0,(m0,m1,m2,m3,m4,n0,n1,n2,n3,n4,u),dp; ideal E=imap(R,E); option(redSB); ideal G=std(E); printf("SR(%d,%d) chart m%d minor %d: unit %%s dim %%s",reduce(1,G)==0,dim(G)); quit;'%(A,B,k,j))
open('sr_%d%d_%d%d.sing'%(A,B,k,j),'w').write('\n'.join(L)+'\n')
