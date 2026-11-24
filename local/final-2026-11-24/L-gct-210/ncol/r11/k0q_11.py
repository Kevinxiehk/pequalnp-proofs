# K0 sub-case (r_a, r_b) = (1,1): S = span((a,0),(0,b)); defect vectors D (d2), F, G (d3 parts) all = multiples of m; e = 1 via the chart of
# (lambda_D, lambda_F, lambda_G) in P^2 (D = lD m, F = lF m, G = lG m); sum m = 0; Rabinowitsch prod_{j != I} m_j != 0; chart a_0 = 1 (S5).
# usage: python3 -I k0q_11.py LC(0..2) I OUT.sing [char]
import sys
LC=int(sys.argv[1]); I=int(sys.argv[2]); out=sys.argv[3]; CH=sys.argv[4] if len(sys.argv)>4 else '0'
lv=['lD','lF','lG']; lx={l:(l if k!=LC else '1') for k,l in enumerate(lv)}
unk=['a1','a2','a3','a4','b0','b1','b2','b3','b4','m0','m1','m2','m3','m4']+[l for k,l in enumerate(lv) if k!=LC]+(['z'] if I>=0 else [])
L=['ring R = %s, (%s), dp;'%(CH,','.join(unk)),'option(redSB);',
'''proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}
proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}
proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }
list A = 1,a1,a2,a3,a4; list B = b0,b1,b2,b3,b4; list M = m0,m1,m2,m3,m4;
poly SA = 1+a1+a2+a3+a4; poly SB = b0+b1+b2+b3+b4; poly ab = 0; int k; for(k=1;k<=5;k++){ ab = ab + A[k]*B[k]; }
ideal F = e3(A), e3(B), ab - SA*SB, m0+m1+m2+m3+m4;''']
L.append('for(k=1;k<=5;k++){ F = F, SA*B[k]+SB*A[k]-2*A[k]*B[k] - (%s)*M[k], A[k]*e2(dropk(A,k)) - (%s)*M[k], B[k]*e2(dropk(B,k)) - (%s)*M[k]; }'%(lx['lD'],lx['lF'],lx['lG']))
if I>=0: L.append('F = F, 1 - z*%s;'%('*'.join('m%d'%j for j in range(5) if j!=I)))
L.append('int t0 = timer; ideal G = std(F); "VERDICT", ((size(G)==1) && (deg(G[1])==0)), "DIM", dim(G), "SECONDS", timer - t0;')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
