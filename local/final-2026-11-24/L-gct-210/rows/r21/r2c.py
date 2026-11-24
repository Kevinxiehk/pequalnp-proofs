# RANK-2 configurations of (SM_n) in rational coordinates.  f isotropic != 0, columns span a plane U containing f.
#  U degenerate => all columns parallel to f (rank 1, excluded separately).  U nondegenerate => U = span(f, f'), f' the second isotropic
#  line; degree 2 ("g_k = f - 2y_k isotropic") <=> each column is a_k f (k in S0) or f/2 + b_k f' (k in S1, b_k != 0);
#  sum_{S1} b_k = 0, sum_{S0} a_k = 1 - |S1|/2.  f = c(sg), f' = c(sp), sg != sp (IS4: a vertex outside {f, f'} goes to c(inf)).
#  REAL coordinates: c(s) = (s^2-1, s^2+1, 2s), actual Walsh vector D c(s), D = diag(1,i,1); parity split as in planeG.py.
#  Conditions: all t^d (d >= 2) coefficients of perm(J + tY \ col j), j = 1..5.   usage: python3 -I r2c.py P NC S1SIZE OUT
import sys
P,NC,s1,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
EQ=([a[3:] for a in sys.argv[5:] if a.startswith('EQ=')] or [''])[0]   # e.g. EQ=1=2,3=4 : b_1 = b_2, b_3 = b_4
S1=list(range(1,s1+1)); S0=list(range(s1+1,NC+1))
unk=['sg','sp']+['a%d'%k for k in S0]+['b%d'%k for k in S1]+['rz']
L=['ring R=%s,(t,%s,ii),dp; option(redSB);'%(P,','.join(unk))]
L.append('matrix H[4][3]=1,1,1,1,-1,-1,-1,1,-1,-1,-1,1; matrix D[3][3]=1,0,0,0,ii,0,0,0,1; int i; int j; int k; int c;')
L.append('proc cc(poly s){ matrix v[3][1]=s^2-1,s^2+1,2*s; return(v); }')
L.append('matrix f=cc(sg); matrix fp=cc(sp); matrix Y[4][5]; matrix colW[3][1];')
for k in range(1,6):
    if k in S0: L.append('colW=a%d*f; matrix cC%d=H*D*colW; for(i=1;i<=4;i++){ Y[i,%d]=cC%d[i,1]; }'%(k,k,k,k))
    elif k in S1: L.append('colW=f/2+b%d*fp; matrix cC%d=H*D*colW; for(i=1;i<=4;i++){ Y[i,%d]=cC%d[i,1]; }'%(k,k,k,k))
    else: L.append('for(i=1;i<=4;i++){ Y[i,%d]=0; }'%k)
lin=[]
if S1: lin.append('+'.join('b%d'%k for k in S1))
lin.append('2*(%s)-(2-%d)'%('+'.join('a%d'%k for k in S0) if S0 else '0',s1))
eqs=[]
for grp in [g for g in EQ.split(',') if g]:
    ix=grp.split('=')
    eqs+=['b%s-b%s'%(ix[0],x) for x in ix[1:]]
lin+=eqs
L.append('ideal E=%s, rz*(sg-sp)*%s-1;'%(','.join(lin),'*'.join(['a%d'%k for k in S0]+['b%d'%k for k in S1]+['1'])))
L.append('proc perm4(matrix M){ poly s=0; int a1,a2,a3,a4; for(a1=1;a1<=4;a1++){for(a2=1;a2<=4;a2++){ if(a2!=a1){ for(a3=1;a3<=4;a3++){ if((a3!=a1)&&(a3!=a2)){ a4=10-a1-a2-a3; s=s+M[1,a1]*M[2,a2]*M[3,a3]*M[4,a4]; }}}}} return(s);}')
L.append('ideal SI=std(ideal(ii^2+1)); ideal C0; int bad=0; poly g; poly g0; poly g1;')
L.append('for(j=1;j<=5;j++){ matrix M[4][4]; c=0; for(k=1;k<=5;k++){ if(k!=j){ c++; for(i=1;i<=4;i++){ M[i,c]=1+t*Y[i,k]; } } } poly F=perm4(M)-24; matrix T=coeffs(F,t); for(k=3;k<=nrows(T);k++){ g=reduce(T[k,1],SI); g0=subst(g,ii,0); g1=subst(diff(g,ii),ii,0); if((g0!=0) and (g1!=0)){ bad++; } if(g0!=0){C0=C0,g0;} else {C0=C0,g1;} } kill F; kill T; kill M; }')
L.append('printf("parity failures: %s",bad);')
L.append('ring R2=%s,(%s),dp; option(redSB); ideal E=imap(R,C0),imap(R,E);'%(P,','.join(unk)))
L.append('ideal I=std(E); printf("RANK2 n=%d |S1|=%d EQ=%s p=%s: dim %%s unit %%s",dim(I),(reduce(1,I)==0));'%(NC,s1,EQ,P))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
