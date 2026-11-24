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
REFL=[int(a[5:]) for a in sys.argv if a.startswith('REFL=')]   # columns forced to be reflections: s_k = 0, i.e. Q_k(s,.) = 0
for k in REFL:
    L.append('E=E,%s,%s,%s,%s;'%(Q(k,0,0),Q(k,0,1),Q(k,0,2),Q(k,0,3)))
L.append('poly cc=%d; cc=cc/4;'%(s_-(NC-2)))
for r in range(3):
    for k in range(r,3): L.append('E=E,%s%s;'%(VV[r][k],'-cc' if r==k else ''))
    L.append('E=E,%s;'%SV[r])
L.append('CS=CS-(%d)*cub(X); matrix C=coef(CS,x1*x2*x3); int k; for(k=1;k<=ncols(C);k++){E=E,C[2,k];}'%(NC-2))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal G=std(E); printf("SUMQV %s p=%s: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(P,','.join(names),SG+(' REFL='+','.join(map(str,REFL)) if REFL else ''),P))
for c in range(NC):
    if SG[c]=='+': L.append('G=std(sat(G,ideal(%s,%s,%s))); printf("  sat v%d: dim %%s unit %%s",dim(G),(reduce(1,G)==0));'%(Q(c,1,1),Q(c,2,2),Q(c,3,3),c))
L.append('printf("%s SUMQV %s p=%s: unit %%s",(reduce(1,G)==0)); quit;'%('STRATUM' if REFL else 'RESULT',SG+(' REFL='+','.join(map(str,REFL)) if REFL else ''),P))
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
