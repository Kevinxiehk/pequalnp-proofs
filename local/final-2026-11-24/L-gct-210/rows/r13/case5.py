# Support-4 (2,1) kernels: case tree in the Lemma-RS normal form (rows, round 14).  Columns 1..4 = a..d, column 5 zero.
# u = c(s0), w = c'(s0)/2;  f_k = c(sig_k), m_k = ep_k c'(sig_k)/2 + mu_k c(sig_k);  gauges al_1 = 0, mu_1 = 0, be_1 = 1 (1 in supp n).
# CASE P2: sig_2 = sig_1, be_2 = -1, be_3 = be_4 = 0.   CASE P3: sig_2 = sig_3 = sig_1, be_3 = -1 - be_2, be_4 = 0 (be_2 be_3 != 0).
# CASE G : sig_1..sig_4 pairwise distinct, be_2, be_3, be_4 free (Rabinowitsch: distinct, be's nonzero).
# Sums: sum al_k f_k = 2u, sum m_k = 2w, sum be_k f_k = 0.  Conditions: all y-coefficients of P_3, P_4 of every deletion.
# Saturation: column k nonzero (k = 1..4).  Optional MOB=a,b,c,d (Moebius chart of the conic parameter).
# SUPPORT 5 variant (case5.py): columns 1..5 supported; sums = 3u, 3w, 0; cases P2,P3,P4,P5,PP,G4,S23,R4,R5.
# usage: python3 -I case5.py P CASE OUT [MOB=a,b,c,d]
import sys
P,CASE,out=sys.argv[1],sys.argv[2],sys.argv[3]
MOB=[a[4:] for a in sys.argv if a.startswith('MOB=')]
a_,b_,c_,d_=[int(x) for x in MOB[0].split(',')] if MOB else (1,0,0,1)
dt=a_*d_-b_*c_
sig={1:'s1'}
C=CASE
if C=='P2':  sig.update({2:'s1',3:'s3',4:'s4',5:'s5'}); be={1:'1',2:'-1',3:'0',4:'0',5:'0'}; rab='1'
elif C=='P3': sig.update({2:'s1',3:'s1',4:'s4',5:'s5'}); be={1:'1',2:'be2',3:'(-1-be2)',4:'0',5:'0'}; rab='be2*(1+be2)'
elif C=='P4': sig.update({2:'s1',3:'s1',4:'s1',5:'s5'}); be={1:'1',2:'be2',3:'be3',4:'(-1-be2-be3)',5:'0'}; rab='be2*be3*(1+be2+be3)'
elif C=='P5': sig.update({2:'s1',3:'s1',4:'s1',5:'s1'}); be={1:'1',2:'be2',3:'be3',4:'be4',5:'(-1-be2-be3-be4)'}; rab='be2*be3*be4*(1+be2+be3+be4)'
elif C=='PP': sig.update({2:'s1',3:'s3',4:'s3',5:'s5'}); be={1:'1',2:'-1',3:'be3',4:'(-be3)',5:'0'}; rab='be3*(s1-s3)'
elif C=='G4': sig.update({2:'s2',3:'s3',4:'s4',5:'s5'}); be={1:'1',2:'be2',3:'be3',4:'be4',5:'0'}; rab='be2*be3*be4*(s1-s2)*(s1-s3)*(s1-s4)*(s2-s3)*(s2-s4)*(s3-s4)'
elif C=='S23': sig.update({2:'s1',3:'s3',4:'s3',5:'s3'}); be={1:'1',2:'-1',3:'be3',4:'be4',5:'(-be3-be4)'}; rab='be3*be4*(be3+be4)*(s1-s3)'
elif C=='R4': sig.update({2:'s1',3:'s3',4:'s4',5:'s5'}); be={1:'1',2:'be2',3:'be3',4:'be4',5:'be5'}; rab='be2*be3*be4*be5*(1+be2)*(s1-s3)*(s1-s4)*(s1-s5)*(s3-s4)*(s3-s5)*(s4-s5)'
elif C=='R5': sig.update({2:'s2',3:'s3',4:'s4',5:'s5'}); be={1:'1',2:'be2',3:'be3',4:'be4',5:'be5'}; rab='be2*be3*be4*be5*'+'*'.join('(s%d-s%d)'%(i,j) for i in range(1,6) for j in range(i+1,6))
else: raise SystemExit('case?')
svars=sorted(set(v for v in sig.values()))
ZN=[k for k in range(1,6) if be[k]=='0']
SUBZ=([a[5:] for a in sys.argv if a.startswith('SUBZ=')] or [''])[0]
SZ=[int(x) for x in SUBZ.split(',') if x]
STAGED='STAGED' in sys.argv
PLZ=[k for k in ZN if k not in SZ]   # zero-n columns whose PLANE column is nonzero (saturated in the plane stage)
bvars=[v for v in ('be2','be3','be4','be5') if any(v in x for x in be.values())]
unk=['s0']+svars+['ep1','ep2','ep3','ep4','ep5','al2','al3','al4','al5','mu2','mu3','mu4','mu5']+bvars+['ii','rz']
L=['ring R=%s,(y1,y2,y3,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ poly S=%d*s+%d; poly T=%d*s+%d; matrix v[3][1]=S^2-T^2,ii*(S^2+T^2),2*S*T; return(v); }'%(a_,b_,c_,d_))
L.append('proc cd(poly s){ poly S=%d*s+%d; poly T=%d*s+%d; matrix v[3][1]=(%d*S-%d*T),ii*(%d*S+%d*T),(%d*T+%d*S); v=v/%d; return(v); }'%(a_,b_,c_,d_,a_,c_,a_,c_,a_,c_,dt))
L.append('matrix u=cc(s0); matrix w=cd(s0);')
al={1:'0',2:'al2',3:'al3',4:'al4',5:'al5'}; mu={1:'0',2:'mu2',3:'mu3',4:'mu4',5:'mu5'}
for k in range(1,6):
    L.append('matrix f%d=cc(%s); matrix m%d=ep%d*cd(%s)+(%s)*cc(%s); poly al%d_=%s; poly be%d_=%s;'%(k,sig[k],k,k,sig[k],mu[k],sig[k],k,al[k],k,be[k]))
L.append('ideal E=ii^2+1,ep1^2-1,ep2^2-1,ep3^2-1,ep4^2-1,ep5^2-1;')
L.append('matrix S1=%s-3*u; matrix S2=%s-3*w; matrix S3=%s;'%('+'.join('al%d_*f%d'%(k,k) for k in range(1,6)),'+'.join('m%d'%k for k in range(1,6)),'+'.join('be%d_*f%d'%(k,k) for k in range(1,6))))
L.append('for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1],S3[i,1]; }')
L.append('E=E,rz*(%s)-1;'%rab)
for k in SZ: L.append('E=E,s%d-s0,al%d-1;'%(k,k))
if C=='G4' and 'FAM' in sys.argv:   # the four n-directions: every triple t vanishes (deletions 1..4), so e_2 = 0, e_4 = -1 (R14.7; identity chart)
    fam='s1*s2+s1*s3+s2*s3+s1*s4+s2*s4+s3*s4,s1*s2*s3*s4+1'
    L.append('E=E,'+fam+';')
    if STAGED: L.append('EP=EP,'+fam+';')
if STAGED: L.append('ideal EP=ii^2+1,rz*(%s)-1; for(i=1;i<=3;i++){ EP=EP,S1[i,1],S3[i,1]; }'%rab+''.join(' EP=EP,s%d-s0,al%d-1;'%(k,k) for k in SZ))
if C=='P2' and 'ADD' in sys.argv:   # consequences (support 5, R16.5): columns 3,4,5 orthogonal to sg(d,d) and to sg(d, m_1 - m_2)
    L.append('proc sgv(matrix x, matrix y){ matrix s[3][1]=x[2,1]*y[3,1]+x[3,1]*y[2,1], x[1,1]*y[3,1]+x[3,1]*y[1,1], x[1,1]*y[2,1]+x[2,1]*y[1,1]; return(s); }')
    L.append('matrix sdd=sgv(f1,f1); matrix sdm=sgv(f1,m1-m2);')
    for k in (3,4,5):
        eq='(transpose(sdd)*(u-al%d_*f%d))[1,1],(transpose(sdd)*(w-m%d))[1,1],(transpose(sdm)*(u-al%d_*f%d))[1,1],(transpose(sdm)*(w-m%d))[1,1]'%(k,k,k,k,k,k)
        L.append('E=E,%s;'%eq)
        if STAGED: L.append('EP=EP,(transpose(sdd)*(u-al%d_*f%d))[1,1];'%(k,k))
L.append('matrix Y[4][5]; matrix colW[3][1];')
for k in range(1,6):
    L.append('colW=y1*(u-al%d_*f%d)/2+y2*(w-m%d)/2-y3*be%d_*f%d/2; matrix colC%d=H*colW; for(i=1;i<=4;i++){ Y[i,%d]=colC%d[i,1]; }'%(k,k,k,k,k,k,k,k))
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal CHK; for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y2*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=3){E=E,T[2,k];'+(' if(diff(T[1,k],y2)==0){EP=EP,T[2,k];}' if STAGED else '')+'} else {CHK=CHK,T[2,k];} } kill F; kill T; kill M; }')
cn=[]
for k in range(1,6):
    cn.append('ideal(%s)'%','.join(['(al%d_*f%d-u)[%d,1]'%(k,k,i) for i in (1,2,3)]+['(m%d-w)[%d,1]'%(k,i) for i in (1,2,3)]+['be%d_'%k]))
L.append('list CN=%s;'%','.join(cn))
if STAGED: L.append('list PZ; '+' '.join('matrix pz%d=al%d_*f%d-u; PZ[%d]=ideal(pz%d[1,1],pz%d[2,1],pz%d[3,1]);'%(k,k,k,i+1,k,k,k) for i,k in enumerate(PLZ)))
unk2=unk
L.append('ring R2=%s,(%s),dp; option(redSB); LIB "elim.lib"; ideal E=imap(R,E); ideal CHK=imap(R,CHK); list CN=imap(R,CN);'%(P,','.join(unk2)))
if STAGED: L.append('ideal EP=imap(R,EP); list PZ=imap(R,PZ); ideal IP=std(EP); int q; for(q=1;q<=size(PZ);q++){ IP=std(sat(IP,PZ[q])); } printf("plane stage: dim %s unit %s",dim(IP),reduce(1,IP)==0); E=E+IP;')
L.append('ideal I=std(E); printf("CASE5 %s mob %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0)); printf("  degree<=2 parts reduce to 0: %%s",size(reduce(CHK,I))==0);'%(CASE,MOB[0] if MOB else 'id',P))
L.append('for(k=1;k<=5;k++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[k])); printf("  after saturation by column %s nonzero: dim %s unit %s",k,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
