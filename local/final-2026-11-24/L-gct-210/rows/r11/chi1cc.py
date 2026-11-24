# (4,1) spaces L' = K (+) C Z with ker c = K = chi (x) C^M (strongly level, row-sum rank 1), chi = (1,i,-1,-i), M = {0,1,2}.
# Unknowns: Z (gauge Z[0][a] = 0 for a in M), m (m_0 = 1 chart), ii (ii^2 = -1).  Conditions: c(Z) = m, and all (w0,w1,w2,t)-
# coefficients of c_j(Y) - m_j c_0(Y), j = 1..4, Y = chi w^T + t Z.  Question: is I : (m1 m2 m3 m4)^inf the unit ideal?
# (unit <=> every such (4,1) space has a zero entry of m, i.e. a NEUTRAL column).   usage: python3 chigen.py P OUT [cal]
import sys
P=sys.argv[1]; out=sys.argv[2]; K0=int(sys.argv[3]); cal=len(sys.argv)>4   # K0 = index with m_K0 = 1
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5) if not (i==0 and j<3)]
mv=['m%d'%k for k in range(5) if k!=K0]
unk=zs+mv+['ii']
L=['ring R=%s,(w0,w1,w2,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5):
        if not (i==0 and j<3): L.append('Z[%d,%d]=z%d%d;'%(i+1,j+1,i,j))
L.append('list chi=1,ii,-1,-ii; list w=w0,w1,w2,0,0; list mm=%s;'%','.join('1' if k==K0 else 'm%d'%k for k in range(5)))
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){for(j=1;j<=5;j++){ Y[i,j]=chi[i]*w[j]+t*Z[i,j]; }}')
L.append('proc perm4(matrix M){ poly s=0; int p1,p2,p3,p4;')
L.append(' for(p1=1;p1<=4;p1++){for(p2=1;p2<=4;p2++){ if(p2!=p1){ for(p3=1;p3<=4;p3++){ if((p3!=p1)&&(p3!=p2)){ p4=10-p1-p2-p3;')
L.append('   s=s+M[1,p1]*M[2,p2]*M[3,p3]*M[4,p4]; }}}}}')
L.append(' return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E;')
L.append('for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){ cs=cs+Z[i,j]; } E=E,cs; }')   # column sums of Z = m
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d];'%(K0+1,K0+1)+' matrix T=coef(F,w0*w1*w2*t); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; } kill F; kill T; } }')
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E);'%(P,','.join(unk)))
L.append('ideal I=E,ii^2+1,1+%s; I=std'%('+'.join(mv))+'(simplify(I,2+4+8)); printf("CHI p=%s: dim %%s unit %%s size %%s",dim(I),(reduce(1,I)==0),size(I));'%P)
if cal:
    imp=','.join(('m%d+1'%k if k==4 else 'm%d'%k) for k in range(5) if k!=K0)
    L.append('ideal G2=std(I+ideal(%s)); printf("CHI CAL p=%s: with m = e_%d - e_4 imposed: dim %%s unit %%s",dim(G2),(reduce(1,G2)==0));'%(imp,P,K0))
L.append('I=std(sat(I,ideal(%s))); printf("CHI1-CC (column-centred, Z != 0): dim %%s unit %%s",dim(I),(reduce(1,I)==0)); ideal Em=eliminate(I,%s); print(Em);'%(','.join(zs),'*'.join(zs)))
L.append('ideal S=sat(I,ideal(%s));'%('*'.join(mv))+' S=std(S); printf("CHI p=%s: after saturation by m1 m2 m3 m4: dim %%s unit %%s",dim(S),(reduce(1,S)==0));'%P)
L.append('if(size(S)<40){print(S);}')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
