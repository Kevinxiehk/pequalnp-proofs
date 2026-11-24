# CONJECTURE K0, base-point-free pencil case, normal form iota = diag(1,-1):  l_j = al_j x + ap_j y,  lam_j = k_j (al_j x - ap_j y).
# Writes a Singular script over Q (or char P) with the equations (Q1), (D2), (L2), (P3), (D3) (NOTES R10.1); chart al_J1 = 1, ap_J2 = 1.
# usage: python3 -I k0bpf.py CHAR J1 J2 OUT.sing [mode: gb | minass]
import sys
P=int(sys.argv[1]); J1=int(sys.argv[2]); J2=int(sys.argv[3]); out=sys.argv[4]; mode=sys.argv[5] if len(sys.argv)>5 else 'gb'
al=['1' if j==J1 else 'al%d'%j for j in range(5)]; ap=['1' if j==J2 else 'ap%d'%j for j in range(5)]
unk=[v for v in ['al%d'%j for j in range(5)] if v!='al%d'%J1]+[v for v in ['ap%d'%j for j in range(5)] if v!='ap%d'%J2]+['k%d'%j for j in range(5)]+['m%d'%j for j in range(5)]+['c','d','g0','g1','g2','g3']
L=['ring R = %d, (%s,x,y), dp;'%(P,','.join(unk)),'option(redSB);']
for j in range(5):
    L.append('poly l%d = (%s)*x + (%s)*y; poly lam%d = k%d*((%s)*x - (%s)*y);'%(j,al[j],ap[j],j,j,al[j],ap[j]))
L.append('poly LL = l0+l1+l2+l3+l4; poly MM = lam0+lam1+lam2+lam3+lam4;')
for j in range(5):
    L.append('poly a%d = l%d - LL/3; poly b%d = lam%d - MM/3;'%(j,j,j,j))
L.append('''list A = a0,a1,a2,a3,a4; list B = b0,b1,b2,b3,b4;
proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=5;i++){for(j=i+1;j<=5;j++){s=s+v[i]*v[j];}} return(s);}
proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=5;i++){for(j=i+1;j<=5;j++){for(k=j+1;k<=5;k++){s=s+v[i]*v[j]*v[k];}}} return(s);}
poly SA = a0+a1+a2+a3+a4; poly SB = b0+b1+b2+b3+b4; poly EA = e2(A); poly EB = e2(B);
poly Q2 = c*x^2 + d*y^2; poly Q3 = g0*x^3 + g1*x^2*y + g2*x*y^2 + g3*y^3;
list ms = m0,m1,m2,m3,m4; list ls = l0,l1,l2,l3,l4; list lams = lam0,lam1,lam2,lam3,lam4;
ideal F;
proc addco(poly f){ matrix C = coef(f, x*y); int ii; for(ii=1;ii<=ncols(C);ii++){ F = F, C[2,ii]; } }
int j;
addco(LL*MM - jet(LL*MM,0));   // placeholder removed below
''')
L[-1]=L[-1].replace("addco(LL*MM - jet(LL*MM,0));   // placeholder removed below\n","")
L.append('matrix CLM = coef(LL*MM, x*y); int t; for(t=1;t<=ncols(CLM);t++){ if(CLM[1,t]==x*y){ F = F, CLM[2,t]; } }')   # (Q1) no xy term
L.append('for(j=1;j<=5;j++){ addco(ls[j]*lams[j] - LL*MM/9 - ms[j]*Q2); }')                          # (D2)
L.append('F = F, m0+m1+m2+m3+m4;')                                                                 # (L2)
L.append('addco(e3(A)+e3(B));')                                                                   # (P3)
L.append('for(j=1;j<=5;j++){ addco(-6*(A[j]*(EA - SA*A[j] + A[j]^2) + B[j]*(EB - SB*B[j] + B[j]^2)) - ms[j]*Q3); }')   # (D3)
L.append('F = simplify(F,2+4+8); "NGEN", size(F);')
L.append('ring R2 = %d, (%s), dp; ideal F2 = imap(R, F); option(redSB);'%(P,','.join(unk)))
if mode=='gb':
    L.append('ideal G = std(F2); "DIM", dim(G); "MULT_or_DEG", mult(G);')
else:
    L.append('LIB "primdec.lib"; list pr = minAssGTZ(F2); "NCOMP", size(pr); int q; for(q=1;q<=size(pr);q++){ "COMP", q, "dim", dim(std(pr[q])); int z; string zs=""; for(z=1;z<=5;z++){ if(reduce(var(nvars(basering)-15+z+4),std(pr[q]))==0){ zs = zs + string(z-1) + " "; } } "  m-zeros:", zs; }')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
