# CASE C split: as k0_11C2 (m = F, G = gam F, D = del F, all entries nonzero, a_0 = b_0 = 1), but each shape equality F_i = F_j
# (resp. G_i = G_j) is replaced by ONE factor of F_i - F_j = (a_i - a_j) * (a_i^2 + a_i a_j + a_j^2 - A(a_i + a_j) + e2(a))
# (resp. the b-version).  CODE = 4 letters (E = equal factor, Q = quadric factor) for (F pair1, G pair1, F pair2, G pair2).
# The union over the 16 codes is the whole Case C.  usage: python3 -I k0_11C3.py SH CODE CH OUT.sing
import sys
SH,CODE,CH,out=sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4]
a=['1']+['a%d'%k for k in range(1,5)]; b=['1']+['b%d'%k for k in range(1,5)]; par=a[1:]+b[1:]+['gam','del','z']
pairs=[(0,1),(1,2)] if SH=='a3' else [(0,1),(2,3)]; jj=4 if SH=='a3' else 3
def fac(V,S,E2,i,j,c):
    vi,vj='%s[%d]'%(V,i+1),'%s[%d]'%(V,j+1)
    return '(%s - %s)'%(vi,vj) if c=='E' else '(%s^2 + %s*%s + %s^2 - %s*(%s + %s) + %s)'%(vi,vi,vj,vj,S,vi,vj,E2)
eqs=[]
for n,(i,j) in enumerate(pairs):
    eqs.append(fac('A','SA','e2(A)',i,j,CODE[2*n])); eqs.append(fac('B','SB','e2(B)',i,j,CODE[2*n+1]))
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'ring R = %s, (%s), dp; option(redSB);'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(a),','.join(b)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'list D; list F; list G; for(k=1;k<=5;k++){ D = insert(D, SA*B[k]+SB*A[k]-2*A[k]*B[k], size(D)); F = insert(F, A[k]*e2(dropk(A,k)), size(F)); G = insert(G, B[k]*e2(dropk(B,k)), size(G)); }',
'ideal I0 = e3(A), e3(B), ab - SA*SB, %s, 1 - z*gam*F[1]*F[%d]*F[5];'%(', '.join(eqs),jj),
'for(k=1;k<=5;k++){ I0 = I0, G[k] - gam*F[k], D[k] - del*F[k]; }',
'int t0 = timer; ideal Gb = std(I0); "STD", "%s", "unit", ((size(Gb)==1) && (deg(Gb[1])==0)), "dim", dim(Gb), "vdim", vdim(Gb), "SECONDS", timer - t0;'%CODE,
'if(!((size(Gb)==1) && (deg(Gb[1])==0))){ list pr = minAssGTZ(Gb); "NCOMP", size(pr); int q;',
'  for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); "COMP", q, "dim", dim(P), "vdim", vdim(P); P; kill P; } }',
'quit;']
open(out,'w').write('\n'.join(L)+'\n')
