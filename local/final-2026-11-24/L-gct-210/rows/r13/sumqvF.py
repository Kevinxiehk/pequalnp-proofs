# SUMQ in VERONESE variables (rows, round 13): Q_j = q_j q_j^T (q_j = (s_j, a_j, b_j, d_j) unit quaternion) removes the 2^NC sign symmetry;
# B_j = eps_j Ad(q_j) is LINEAR in Q_j, the frame equations and the norms are LINEAR, the summed cubic is CUBIC, and rank Q_j <= 1 is given by
# the 2x2 minors.  Same content as sumq.py (degree-2 quaternion data + summed cubic sum_j c(B_j x) = (NC-2) c(x)).
# usage: python3 -I sumqv.py SG OUT [P]
import sys, itertools
SG=sys.argv[1]; out=sys.argv[2]; P=sys.argv[3] if len(sys.argv)>3 else '0'; NC=len(SG)
s_=sum(1 if x=='+' else -1 for x in SG)
idx=['s','a','b','d']; pairs=[(i,j) for i in range(4) for j in range(i,4)]
names=['q%d_%s%s'%(c,idx[i],idx[j]) for c in range(NC) for (i,j) in pairs]
def Q(c,i,j):
    i,j=min(i,j),max(i,j); return 'q%d_%s%s'%(c,idx[i],idx[j])
L=['ring R=%s,(%s,x1,x2,x3),dp; option(redSB);'%(P,','.join(names)),'matrix X[3][1]=x1,x2,x3; ideal E; poly CS=0;']
L.append('proc cub(matrix y){ return(y[1,1]*y[2,1]*y[3,1]); }')
VV=[['0']*3 for _ in range(3)]; SV=['0']*3
for c in range(NC):
    e=1 if SG[c]=='+' else -1
    ss,aa,bb,dd=[Q(c,k,k) for k in range(4)]
    L.append('E=E,%s+%s+%s+%s-1;'%(ss,aa,bb,dd))
    # rank <= 1: 2x2 minors of the symmetric 4x4 matrix
    for (i,j),(k,l) in itertools.combinations([(i,j) for i in range(4) for j in range(4)],2):
        pass
    M=[[Q(c,i,j) for j in range(4)] for i in range(4)]
    mins=set()
    for (r1,r2) in itertools.combinations(range(4),2):
        for (c1,c2) in itertools.combinations(range(4),2):
            mins.add('%s*%s-%s*%s'%(M[r1][c1],M[r2][c2],M[r1][c2],M[r2][c1]))
    L.append('E=E,%s;'%','.join(sorted(mins)))
    # Ad(q) for q = s + v (v = (a,b,d)): (s^2 - |v|^2) I + 2 v v^T + 2 s [v]_x, in Q-variables
    v=[1,2,3]
    B=[[None]*3 for _ in range(3)]
    for r in range(3):
        for k in range(3):
            t='2*%s'%Q(c,v[r],v[k])
            if r==k: t+='+%s-(%s+%s+%s)'%(ss,aa,bb,dd)
            B[r][k]=t
    # [v]_x = [[0,-d,b],[d,0,-a],[-b,a,0]]; s*v components: Q(c,0,1)=s a, Q(c,0,2)=s b, Q(c,0,3)= s d
    sa,sb,sd=Q(c,0,1),Q(c,0,2),Q(c,0,3)
    cx=[['0','-2*%s'%sd,'2*%s'%sb],['2*%s'%sd,'0','-2*%s'%sa],['-2*%s'%sb,'2*%s'%sa,'0']]
    L.append('matrix B%d[3][3]=%s; B%d=(%d)*B%d; CS=CS+cub(B%d*X);'%(c,','.join('(%s)+(%s)'%(B[r][k],cx[r][k]) for r in range(3) for k in range(3)),c,e,c,c))
    for r in range(3):
        for k in range(r,3): VV[r][k]+='+(%d)*%s'%(e,Q(c,v[r],v[k]))
        SV[r]+='+(%d)*%s'%(e,Q(c,0,v[r]))
L.append('poly cc=%d; cc=cc/4;'%(s_-(NC-2)))
for r in range(3):
    for k in range(r,3): L.append('E=E,%s%s;'%(VV[r][k],'-cc' if r==k else ''))
    L.append('E=E,%s;'%SV[r])
FULL='FULL' in sys.argv; Q4='Q4' in sys.argv
if not FULL:
    L.append('CS=CS-(%d)*cub(X); matrix C=coef(CS,x1*x2*x3); int k; for(k=1;k<=ncols(C);k++){E=E,C[2,k];}'%(NC-2))
else:
    L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix Yc[4][5]; int k; int jj; int ii2;')
    for c in range(NC):
        L.append('matrix yc%d=H*(X-B%d*X)/2; for(ii2=1;ii2<=4;ii2++){ Yc[ii2,%d]=yc%d[ii2,1]; }'%(c,c,c+1,c))
    L.append('proc t3c(matrix a, matrix b, matrix c){ poly q=0; int r; for(r=1;r<=4;r++){ q=q+a[r,1]*b[r,1]*c[r,1]; } return(q); }')
    L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
    L.append('list cols; for(jj=1;jj<=5;jj++){ matrix cj[4][1]; for(ii2=1;ii2<=4;ii2++){ cj[ii2,1]=Yc[ii2,jj]; } cols[jj]=cj; kill cj; }')
    L.append('int d1,d2,d3,d4; for(k=1;k<=5;k++){ poly F3=0; for(d1=1;d1<=5;d1++){ for(d2=d1+1;d2<=5;d2++){ for(d3=d2+1;d3<=5;d3++){ if((d1!=k)&&(d2!=k)&&(d3!=k)){ F3=F3+t3c(cols[d1],cols[d2],cols[d3]); } } } } matrix C=coef(F3,x1*x2*x3); for(jj=1;jj<=ncols(C);jj++){E=E,C[2,jj];} kill C; kill F3; }')
    if Q4: L.append('for(k=1;k<=5;k++){ matrix M4[4][4]; int cc2=0; for(jj=1;jj<=5;jj++){ if(jj!=k){ cc2++; for(ii2=1;ii2<=4;ii2++){ M4[ii2,cc2]=Yc[ii2,jj]; } } } poly F4=perm4(M4); matrix C=coef(F4,x1*x2*x3); for(jj=1;jj<=ncols(C);jj++){E=E,C[2,jj];} kill C; kill F4; kill M4; kill cc2; }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal G=std(E); printf("SUMQV%s %s p=%s: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(P,','.join(names),'F' if FULL else '',SG,P))
for c in range(NC):
    if SG[c]=='+': L.append('G=std(sat(G,ideal(%s,%s,%s))); printf("  sat v%d: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(Q(c,1,1),Q(c,2,2),Q(c,3,3),c))
L.append('printf("RESULT SUMQV %s p=%s: unit %%s",(reduce(1,G)==0)); quit;'%(SG,P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
