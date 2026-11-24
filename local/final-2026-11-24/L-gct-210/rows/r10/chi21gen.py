# (4,1) spaces L' = K (+) C Z over the TWO-COLUMN (2,1) kernels K = span{u(e0+e1)^T, (p+e)e0^T + (p-e)e1^T, d0(e0-e1)^T} (Walsh coordinates,
# dot product): u = (al^2-1, ii(al^2+1), 2al) [chart; UCH = 0: u = (1,ii,0)], d0 likewise with ga [DCH], u.p = 0, p.p = 1, d0.e = 0, e.e = 1.
# Z free (no gauge), m with chart m_K0 = 1.  Output: dim, and saturation by prod(other m_j) (unit <=> m has a zero entry: a NEUTRAL column).
import sys
P,UCH,DCH,K0,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
zs=['z%d%d'%(i,j) for i in range(4) for j in range(5)]
mv=['m%d'%k for k in range(5) if k!=K0]
unk=['al','ga','p1','p2','p3','e1','e2','e3','ii']+zs+mv
L=['ring R=%s,(sa,sb,sc,t,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1;')
L.append('matrix uW[3][1]=%s; matrix dW[3][1]=%s; matrix pW[3][1]=p1,p2,p3; matrix eW[3][1]=e1,e2,e3;'%(
  'al^2-1,ii*(al^2+1),2*al' if UCH else '1,ii,0', 'ga^2-1,ii*(ga^2+1),2*ga' if DCH else '1,ii,0'))
L.append('matrix u=H*uW; matrix d=H*dW; matrix pp=H*pW; matrix ee=H*eW;')
L.append('matrix Z[4][5]; int i; int j; int k; int c;')
for i in range(4):
    for j in range(5): L.append('Z[%d,%d]=z%d%d;'%(i+1,j+1,i,j))
L.append('list mm=%s;'%','.join('1' if k==K0 else 'm%d'%k for k in range(5)))
L.append('matrix Y[4][5]; for(i=1;i<=4;i++){ Y[i,1]=sa*u[i,1]+sb*(pp[i,1]+ee[i,1])+sc*d[i,1]; Y[i,2]=sa*u[i,1]+sb*(pp[i,1]-ee[i,1])-sc*d[i,1]; for(j=1;j<=5;j++){Y[i,j]=Y[i,j]+t*Z[i,j];} }')
L.append('proc perm4(matrix M){ poly s=0; int p1_,p2_,p3_,p4_; for(p1_=1;p1_<=4;p1_++){for(p2_=1;p2_<=4;p2_++){ if(p2_!=p1_){ for(p3_=1;p3_<=4;p3_++){ if((p3_!=p1_)&&(p3_!=p2_)){ p4_=10-p1_-p2_-p3_; s=s+M[1,p1_]*M[2,p2_]*M[3,p3_]*M[4,p4_]; }}}}} return(s);}')
L.append('list CC; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } CC[j]=perm4(M)-24; kill M; }')
L.append('ideal E; for(j=1;j<=5;j++){ poly cs=0; for(i=1;i<=4;i++){cs=cs+Z[i,j];} E=E,cs-mm[j]; }')
L.append('for(j=1;j<=5;j++){ if(j!=%d){ poly F=CC[j]-mm[j]*CC[%d]; matrix T=coef(F,sa*sb*sc*t); for(k=1;k<=ncols(T);k++){E=E,T[2,k];} kill F; kill T; } }'%(K0+1,K0+1))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E);'%(P,','.join(unk)))
L.append('ideal I=E,ii^2+1,1+%s, p1*(%s)+p2*(%s)+p3*(%s), p1^2+p2^2+p3^2-1, e1*(%s)+e2*(%s)+e3*(%s), e1^2+e2^2+e3^2-1;'%(
  '+'.join(mv),
  *(['al^2-1','ii*(al^2+1)','2*al'] if UCH else ['1','ii','0']),
  *(['ga^2-1','ii*(ga^2+1)','2*ga'] if DCH else ['1','ii','0'])))
L.append('I=std(I); printf("CHI21 u%d d%d m%d p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); if(reduce(1,I)!=0){ ideal S=std(sat(I,ideal(%s))); printf("   after saturation by the other m_j (no zero entry): dim %%s unit %%s",dim(S),(reduce(1,S)==0)); }'%(UCH,DCH,K0,P,'*'.join(mv)))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
