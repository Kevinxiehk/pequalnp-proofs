# Exact system for (2,1) kernels in the Lemma-RS normal form (rows, round 13).
# Conic c(s) = (s^2-1, ii(s^2+1), 2s) (Walsh), c'(s)/2 = (s, ii s, 1).  u = c(s0), w = c'(s0)/2; column k: f_k = c(sk),
# m_k = ep_k c'(sk)/2 + mu_k c(sk) (ep_k^2 = 1), al_k, be_k; gauges be_1 = 1, al_1 = 0, mu_1 = 0.
# Columns: A_k e1 = (u - al_k f_k)/2, A_k e2 = (w - m_k)/2, A_k n = -be_k f_k/2; sums sum al_k f_k = 3u, sum m_k = 3w, sum be_k f_k = 0.
# SUP = 4: column 5 zero (al_5 f_5 = u: s5 = s0, al_5 = 1, mu_5 = 0, ep_5 = 1, be_5 = 0).  Conditions: all y-coefficients of P_3, P_4 of every
# deletion (P_2 automatic -- also imposed as a check).  Then saturate by "column k nonzero" (k in the support).
# usage: python3 -I k21sys.py P SUP OUT
import sys
P,SUP,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
S0=[a[3:] for a in sys.argv if a.startswith('S0=')]
NS=SUP
cs=list(range(1,NS+1))
unk=['s0']+['s%d'%k for k in cs]+['ep%d'%k for k in cs]+['al%d'%k for k in cs if k>1]+['be%d'%k for k in cs if k>1]+['mu%d'%k for k in cs if k>1]+['ii']
L=['ring R=%s,(y1,y2,y3,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ matrix v[3][1]=s^2-1,ii*(s^2+1),2*s; return(v); }')
L.append('proc cd(poly s){ matrix v[3][1]=s,ii*s,1; return(v); }')
L.append('matrix u=cc(s0); matrix w=cd(s0);')
def par(name,k,default):
    return default if k==1 else '%s%d'%(name,k)
for k in range(1,6):
    if k<=NS:
        al=par('al',k,'0'); be=par('be',k,'1'); mu=par('mu',k,'0'); ep='ep%d'%k
        L.append('matrix f%d=cc(s%d); matrix m%d=(%s)*cd(s%d)+(%s)*cc(s%d); poly al%d_=%s; poly be%d_=%s;'%(k,k,k,ep,k,mu,k,k,al,k,be))
    else:
        L.append('matrix f%d=u; matrix m%d=w; poly al%d_=1; poly be%d_=0;'%(k,k,k,k))
L.append('ideal E=ii^2+1;'+(' E=E,s0-(%s);'%S0[0] if S0 else ''))
for k in cs:
    L.append('E=E,ep%d^2-1;'%k)
L.append('matrix S1=%s-3*u; matrix S2=%s-3*w; matrix S3=%s;'%('+'.join('al%d_*f%d'%(k,k) for k in range(1,6)),'+'.join('m%d'%k for k in range(1,6)),'+'.join('be%d_*f%d'%(k,k) for k in range(1,6))))
L.append('for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1],S3[i,1]; }')
L.append('matrix Y[4][5]; matrix colW[3][1];')
for k in range(1,6):
    L.append('colW=y1*(u-al%d_*f%d)/2+y2*(w-m%d)/2-y3*be%d_*f%d/2; matrix colC%d=H*colW; for(i=1;i<=4;i++){ Y[i,%d]=colC%d[i,1]; }'%(k,k,k,k,k,k,k,k))
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal CHK; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y2*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=3){E=E,T[2,k];} else {CHK=CHK,T[2,k];} } kill F; kill T; kill M; }')
cn=[]
for k in cs:
    cn.append('ideal(%s)'%','.join(['(al%d_*f%d-u)[%d,1]'%(k,k,i) for i in (1,2,3)]+['(m%d-w)[%d,1]'%(k,i) for i in (1,2,3)]+['be%d_'%k]))
L.append('list CN=%s;'%','.join(cn))
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal CHK=imap(R,CHK); list CN=imap(R,CN);'%(P,','.join(unk)))
L.append('ideal I=std(E); printf("K21SYS SUP %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); printf("  degree<=2 parts reduce to 0 mod I: %%s",size(reduce(CHK,I))==0);'%(SUP,P))
L.append('for(k=1;k<=size(CN);k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after saturation by column %s nonzero: dim %s unit %s",k,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
