# verify2 r12: independent generator for stage3 33(J) ((alpha0), |supp W| = 2): the plane
#   P2 = {(s/2)(1,1,1,1,-2) + (c2(s)/2) n2 (e2 - e4) + (c3(s)/2) n3 (e3 - e4) : s in S2},  S2 in Gr(2,V) (3 charts), c2, c3 linear on S2,
# n2 = chi_1 (WLOG by row S_4), n3 in the 6 special lines; all elements must have defect in C m0 (C_j = C_0 (j<4), C_4 + 4 C_0 = 120).
# usage: p2_mine.py CHART N3 TDEG
import sys, itertools, sympy as sp
I=sp.I
base=[1,I,-1,-I]; lines=[]
for p in itertools.permutations(range(4)):
    v=sp.Matrix([base[k] for k in p])
    if not any(sp.Matrix.hstack(v,w).rank(simplify=True)<2 for w in lines): lines.append(v)
ch,n3i,TDEG=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
q=lambda e: str(sp.expand(e)).replace('**','^')
n2=lines[0]; n3=lines[n3i]
basisV={0:(['1','0','a'],['0','1','b']),1:(['1','a','0'],['0','b','1']),2:(['a','1','0'],['b','0','1'])}[ch]
def full4(v3): return v3+['(-(%s)-(%s)-(%s))'%tuple(v3)]
sa,sb=full4(basisV[0]),full4(basisV[1])
L=['ring R=(0,I),(a,b,c2a,c2b,c3a,c3b,t,x1,x2),dp; minpoly=I^2+1;','matrix Y[4][5];']
mm=[1,1,1,1,-2]
for r in range(4):
    for j in range(5):
        e='(x1*(%s)+x2*(%s))*(%d)/2'%(sa[r],sb[r],mm[j])
        if j in (2,4): e+='+(%d)*(x1*c2a+x2*c2b)*(%s)/2'%(1 if j==2 else -1,q(n2[r]))
        if j in (3,4): e+='+(%d)*(x1*c3a+x2*c3b)*(%s)/2'%(1 if j==3 else -1,q(n3[r]))
        L.append('Y[%d,%d]=%s;'%(r+1,j+1,e))
P4=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    L.append('poly C%d=%s;'%(jd,'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[p[r]]+1) for r in range(4)) for p in P4)))
L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E; int k; int j; matrix M; poly g;')
L.append('for(k=1;k<=4;k++){ g=jet(D[k],%d,intvec(0,0,0,0,0,0,1,0,0)); M=coef(g,t*x1*x2); for(j=1;j<=ncols(M);j++){E=E,M[2,j];} }'%TDEG)
L.append('ring R2=(0,I),(a,b,c2a,c2b,c3a,c3b),dp; minpoly=I^2+1; ideal E=imap(R,E); E=simplify(E,2); option(redSB); ideal G=std(E);')
L.append('printf("P2MINE chart %d n3=%d tdeg %d: dim %%s unit %%s",dim(G),reduce(1,G)==0); quit;'%(ch,n3i,TDEG))
open('p2mine_%d_%d_%d.sing'%(ch,n3i,TDEG),'w').write('\n'.join(L)+'\n')
