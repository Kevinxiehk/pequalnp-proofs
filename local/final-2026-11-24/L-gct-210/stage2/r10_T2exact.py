# EXACT (T2) test (Singular over QQ) for a 5-dim space X of 4x5 matrices with entries polynomial in parameters.
# (T2) [NOTES-stage2 R10-1]: exist T_0..T_4 in C^{4x5}, c in C^5 with
#     D_{T_k} G_j(xi) + D_{T_j} G_k(xi) = 0  for all j <= k and all xi in X,     sum_k T_k = J' + sum_m c_m B_m.
# G_j(Y) = perm_4(Y without column j).  Unit ideal  <=>  (T2) unsolvable for EVERY parameter value (affine, char 0: a proof).
# usage: r10_T2exact.py NAME [CHAR]   NAME in S3 (survivor (S3), parameter sg), S2 (z = 3 control), S1pt (M_A_i point, control: solvable)
import sys, itertools
name=sys.argv[1]; ch=sys.argv[2] if len(sys.argv)>2 else '0'
def zero(): return [['0']*5 for _ in range(4)]
par=[]
if name=='S3':
    par=['sg']; B=[zero() for _ in range(5)]
    B[0][0][0]='sg'; B[0][1][0]='(-1-sg)'; B[0][3][0]='1'
    B[1][2]=['-4','1','1','1','1']; B[2][2]=['0','1','-1','0','0']; B[3][3]=['0','0','0','1','-1']; B[4][3]=['0','1','1','-1','-1']
elif name=='S2':   # M_A_ii, d = 0: kappa' + e_3 (x) span{(-4,1,1,1,1),(0,1,-1,0,0),(0,-1,-1,1,1)} + e_4 (x) (0,0,0,1,-1)
    par=['sg']; B=[zero() for _ in range(5)]
    B[0][0][0]='sg'; B[0][1][0]='(-1-sg)'; B[0][3][0]='1'
    B[1][2]=['-4','1','1','1','1']; B[2][2]=['0','1','-1','0','0']; B[3][3]=['0','0','0','1','-1']; B[4][2]=['0','-1','-1','1','1']
elif name=='S1pt': # D04 M_A_i at f0 = f3 = 2 (integer basis)
    B=[zero() for _ in range(5)]
    B[0][0][0]='1'; B[0][1][0]='-1'
    B[1][0][0]='-1'; B[1][1][0]='-1'; B[1][2]=['-4','1','1','1','1']; B[1][3][0]='2'
    B[2][2]=['0','1','-1','0','0']; B[3][3]=['0','0','0','1','-1']
    B[4][0][0]='-1'; B[4][1][0]='-1'; B[4][2]=['0','-1','-1','1','1']; B[4][3][0]='2'
elif name=='PROPD04':   # D0-4 PROP family, dim A = 1: kappa'(sg) + e_3 (x) span{(-4;1'),(0;alpha)} + e_4 (x) (0; alpha^perp cap 1^perp); alpha_1 = 1
    par=['sg','a2','a3']; al=['1','a2','a3','(-1-a2-a3)']
    def det3(M): return '(%s)'%('+'.join(['(%s)*(%s)*(%s)'%(M[0][p[0]],M[1][p[1]],M[2][p[2]]) if s>0 else '-(%s)*(%s)*(%s)'%(M[0][p[0]],M[1][p[1]],M[2][p[2]]) for p,s in [((0,1,2),1),((1,2,0),1),((2,0,1),1),((0,2,1),-1),((2,1,0),-1),((1,0,2),-1)]]))
    W=[]
    for m in range(4):
        em=['1' if c==m else '0' for c in range(4)]; w=[]
        for j in range(4):
            cs=[c for c in range(4) if c!=j]; M=[['1']*3,[al[c] for c in cs],[em[c] for c in cs]]
            w.append(('' if j%2==0 else '-')+det3(M))
        W.append(w)
    B=[zero() for _ in range(2+1+4)]
    B[0][0][0]='sg'; B[0][1][0]='(-1-sg)'; B[0][3][0]='1'
    B[1][2]=['-4','1','1','1','1']; B[2][2]=['0']+al
    for m in range(4): B[3+m][3]=['0']+W[m]
elif name in ('D003A','D003Agen'):   # D003-PROP, Case A (l = (1,-1)): column-0 part {(s,-s,pi,-pi)} + e_3 (x) (0;A) + e_4 (x) (0;A^perp cap 1^perp)
    if name=='D003A': al=['1','-1','0','0']; par=[]
    else: par=['a2','a3']; al=['1','a2','a3','(-1-a2-a3)']
    def det3(M): return '(%s)'%('+'.join(['(%s)*(%s)*(%s)'%(M[0][p[0]],M[1][p[1]],M[2][p[2]]) if s>0 else '-(%s)*(%s)*(%s)'%(M[0][p[0]],M[1][p[1]],M[2][p[2]]) for p,s in [((0,1,2),1),((1,2,0),1),((2,0,1),1),((0,2,1),-1),((2,1,0),-1),((1,0,2),-1)]]))
    W=[]
    for m in range(4):
        em=['1' if c==m else '0' for c in range(4)]; w=[]
        for j in range(4):
            cs=[c for c in range(4) if c!=j]; M=[['1']*3,[al[c] for c in cs],[em[c] for c in cs]]
            w.append(('' if j%2==0 else '-')+det3(M))
        W.append(w)
    B=[zero() for _ in range(3+4)]
    B[0][0][0]='1'; B[0][1][0]='-1'; B[1][2][0]='1'; B[1][3][0]='-1'
    B[2][2]=['0']+al
    for m in range(4): B[3+m][3]=['0']+W[m]
P4=list(itertools.permutations(range(4)))
Tv=['T%d_%d%d'%(k,i,l) for k in range(5) for i in range(4) for l in range(5)]; cv=['c%d'%m for m in range(len(B))]
ZS=['z%d'%(m+1) for m in range(len(B))]
print('ring R=%s,(%s),dp;'%(ch,','.join(Tv+cv+par+ZS)))
print('matrix XI[4][5];')
for i in range(4):
    for l in range(5):
        print('XI[%d,%d]=%s;'%(i+1,l+1,'+'.join('z%d*(%s)'%(m+1,B[m][i][l]) for m in range(len(B)))))
def DG(j,k):   # D_{T_k} G_j (xi): sum over permutations of the 4x4 minor (columns != j) and over the position replaced by T_k
    cols=[c for c in range(5) if c!=j]; terms=[]
    for pp in P4:
        for pos in range(4):
            fac=[]
            for i in range(4):
                if i==pos: fac.append('T%d_%d%d'%(k,i,cols[pp[i]]))
                else: fac.append('XI[%d,%d]'%(i+1,cols[pp[i]]+1))
            terms.append('*'.join(fac))
    return '+'.join(terms)
print('ideal I; matrix C; int kk; poly F;')
for j in range(5):
    for k in range(j,5):
        print('F=%s+%s; C=coef(F,%s); for(kk=1;kk<=ncols(C);kk++){I=I+ideal(C[2,kk]);}'%(DG(j,k),DG(k,j),'*'.join(ZS)))
for i in range(4):
    for l in range(5):
        print('I=I+ideal(%s-1-(%s));'%('+'.join('T%d_%d%d'%(k,i,l) for k in range(5)),'+'.join('c%d*(%s)'%(m,B[m][i][l]) for m in range(len(B)))))
print('int t=timer; ideal G=std(I); "T2 EXACT %s char %s: unit (=T2 unsolvable for all parameters):",(reduce(1,G)==0),", size",size(G),", sec",timer-t;'%(name,ch))
if par:
    print('poly tt=1; int ii; for(ii=1;ii<=%d;ii++)'%(100+len(B))+'{tt=tt*var(ii);} ideal E=std(eliminate(I,tt)); "parameter locus where (T2) is solvable:"; E;')
print('quit;')
