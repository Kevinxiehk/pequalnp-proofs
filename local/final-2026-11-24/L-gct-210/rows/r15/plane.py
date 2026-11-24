# THE PLANE TEST (rows, round 15).  K_0 = span(e1, n) inside a (2,1) kernel K is a strongly level PLANE with row sums C u (u isotropic):
#   columns of n: n_k = be_k c(s_k) (sum n_k = 0), columns of e1: (u - a_k n_k)/2 with sum_k a_k n_k = 2u, gauge a_1 = 0, be_1 = 1.
# In case G (support 4) every column of K_0 is nonzero (n_k != 0), so "no such plane" excludes case G.  Support SUP = 4 or 5 columns.
# Conditions: all (y1,y3)-coefficients of P_2, P_3, P_4 of every deletion for Y = y1 e1 + y3 n.  Rabinowitsch: s_k distinct, be_k != 0.
# usage: python3 -I plane.py P SUP OUT [MOB=a,b,c,d]
import sys
P,SUP,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
MOB=[a[4:] for a in sys.argv if a.startswith('MOB=')]
a_,b_,c_,d_=[int(x) for x in MOB[0].split(',')] if MOB else (1,0,0,1)
ks=list(range(1,SUP+1))
PAT=([a[4:] for a in sys.argv if a.startswith('PAT=')] or ['G'])[0]
sig={k:'s%d'%k for k in ks}
if PAT=='P5': sig={k:'s1' for k in ks}
if PAT=='S23': sig={1:'s1',2:'s1',3:'s3',4:'s3',5:'s3'}
if PAT=='R4': sig={1:'s1',2:'s1',3:'s3',4:'s4',5:'s5'}
ZERO=[]   # columns whose n-entry is zero: e1-column (u - al_k c(t_k))/2, saturated to be nonzero
if PAT=='P2_4': sig={1:'s1',2:'s1'}; ZERO=[3,4]
if PAT=='P2_2': sig={1:'s1',2:'s1'}
if PAT=='P2_3': sig={1:'s1',2:'s1'}; ZERO=[3]
if PAT=='P4_4': sig={1:'s1',2:'s1',3:'s1',4:'s1'}
if PAT=='PP_4': sig={1:'s1',2:'s1',3:'s3',4:'s3'}
if PAT=='P4_5': sig={1:'s1',2:'s1',3:'s1',4:'s1'}; ZERO=[5]
if PAT=='PP_5': sig={1:'s1',2:'s1',3:'s3',4:'s3'}; ZERO=[5]
if PAT=='G4_5': sig={1:'s1',2:'s2',3:'s3',4:'s4'}; ZERO=[5]
if PAT=='P3_5': sig={1:'s1',2:'s1',3:'s1'}; ZERO=[4,5]
if PAT=='P2_5': sig={1:'s1',2:'s1'}; ZERO=[3,4,5]
sv=sorted(set(sig.values()))
NK=[k for k in ks if k not in ZERO]
unk=['s0']+sv+['be%d'%k for k in NK if k>1]+['a%d'%k for k in NK if k>1]+['t%d'%k for k in ZERO]+['al%d'%k for k in ZERO]+['ii','rz']
L=['ring R=%s,(y1,y3,%s),dp; option(redSB); LIB "elim.lib";'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ poly S=%d*s+%d; poly T=%d*s+%d; matrix v[3][1]=S^2-T^2,ii*(S^2+T^2),2*S*T; return(v); }'%(a_,b_,c_,d_))
L.append('matrix u=cc(s0);')
for k in NK:
    L.append('matrix n%d=%s*cc(%s); poly a%d_=%s;'%(k,'1' if k==1 else 'be%d'%k,sig[k],k,'0' if k==1 else 'a%d'%k))
for k in ZERO:
    L.append('matrix n%d[3][1]; matrix g%d=al%d*cc(t%d);'%(k,k,k,k))
L.append('ideal E=ii^2+1; matrix S1=%s; matrix S2=%s-%d*u; for(i=1;i<=3;i++){ E=E,S1[i,1],S2[i,1]; }'%('+'.join('n%d'%k for k in NK),'+'.join(['a%d_*n%d'%(k,k) for k in NK]+['g%d'%k for k in ZERO]),SUP-2))
dif='*'.join(['(%s-%s)'%(x,y) for x in sv for y in sv if x<y]+['1'])
if PAT=='P5': dif='1'
if PAT=='S23': dif='(s1-s3)'
if PAT=='R4': dif=dif+'*(1+be2)'
L.append('E=E,rz*%s*%s-1;'%('*'.join(['be%d'%k for k in NK if k>1]+['1']),dif))
if 'FAM' in sys.argv and (SUP==4 or PAT=='G4_5') and not MOB: L.append('E=E,s1*s2+s1*s3+s2*s3+s1*s4+s2*s4+s3*s4,s1*s2*s3*s4+1;')   # case-G point family (R14.7), identity chart
if 'VERT' in sys.argv:   # all points are octahedral vertices: S T (S^4 - T^4) = 0 in the chart parameter (S = a s + b, T = c s + d)
    vs=['s0']+sv+['t%d'%k for k in ZERO]
    for v in vs: L.append('E=E,(%d*%s+%d)*(%d*%s+%d)*((%d*%s+%d)^4-(%d*%s+%d)^4);'%(a_,v,b_,c_,v,d_,a_,v,b_,c_,v,d_))
L.append('matrix Y[4][5]; matrix colW[3][1];')
for k in range(1,6):
    if k in ZERO: L.append('colW=y1*(u-g%d)/2; matrix cC%d=H*colW; for(i=1;i<=4;i++){ Y[i,%d]=cC%d[i,1]; }'%(k,k,k,k))
    elif k<=SUP: L.append('colW=y1*(u-a%d_*n%d)/2-y3*n%d/2; matrix cC%d=H*colW; for(i=1;i<=4;i++){ Y[i,%d]=cC%d[i,1]; }'%(k,k,k,k,k,k))
    else: L.append('for(i=1;i<=4;i++){ Y[i,%d]=0; }'%k)
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
STAGED='STAGED' in sys.argv
L.append('ideal EP=E;')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coef(F,y1*y3); for(k=1;k<=ncols(T);k++){ if(deg(T[1,k])>=2){E=E,T[2,k]; if(deg(subst(T[1,k],y3,1))<=1){EP=EP,T[2,k];} } } kill F; kill T; kill M; }')
if ZERO: L.append('list CN; '+' '.join('matrix dz%d=g%d-u; CN[%d]=ideal(dz%d[1,1],dz%d[2,1],dz%d[3,1]);'%(k,k,i+1,k,k,k) for i,k in enumerate(ZERO)))
L.append(('ring R2=%s,(%s),dp; option(redSB); '%(P,','.join(unk)))+('list CN=imap(R,CN); ' if ZERO else '')+('ideal E=imap(R,E); '+('ideal EP=imap(R,EP); ideal IP=std(EP); printf("stage 1 (y1-degree <= 1): dim %s unit %s",dim(IP),reduce(1,IP)==0); E=E+IP; ' if STAGED else '')+'ideal I=std(E); printf("PLANE SUP %s pat %s mob %s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(SUP,PAT,MOB[0] if MOB else 'id',P)))
if ZERO: L.append('int q; for(q=1;q<=size(CN);q++){ if(reduce(1,I)!=0){ I=std(sat(I,CN[q])); printf("  after saturation by plane column nonzero (%s): dim %s unit %s",q,dim(I),(reduce(1,I)==0)); } }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
