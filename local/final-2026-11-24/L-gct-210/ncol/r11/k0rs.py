# RESTRICTED K0 (round 11, after K0 was found false): classify 2-dim zero-row column-centred level spaces S with e = 1 whose defect
# line m has the a3 shape (m0 = m1 = m2) or the b22 shape (m0 = m1, m2 = m3) and is ZERO-FREE (Rabinowitsch over all m_j).
# Charts: 'P:i,j' = Pluecker chart (a_i, a_j) of Gr(2,10) [r_a = 2; r_b = 2 by the swap a <-> b, which preserves m];
#         '11:I,J' = S = span((u,0),(0,p)), u_I = 1, p_J = 1 [r_a = r_b = 1].   e = 1 via chart QC of (Q2, Q3) in P^6.
# Output: VERDICT 1 (unit: no such S in this chart) or VERDICT 0 + DIM + VDIM, and the reduced GB in <OUT>.gb (to list the members).
# SPLIT (k0rs.py): for each shape pair (i,j) one letter in {S0,S1,X0,X1}: S = 'same' (c0 l_j = c1 l_i, c1 lam_j = c0 lam_i), X = 'crossed'
# (c0 l_j = c1 lam_i, c1 lam_j = c0 l_i), digit = chart (0: c0 = 1, 1: c1 = 1); l = a - A/2, lam = b - B/2 (forms on S).  Union = all (R11.15).
# usage: python3 -I k0rs.py SH(a3|b22) CHART QC SPLIT(e.g. S0X1) OUT.sing [char]
import sys
SH,CHART,QC,SPL,out=sys.argv[1],sys.argv[2],int(sys.argv[3]),sys.argv[4],sys.argv[5]; CH=sys.argv[6] if len(sys.argv)>6 else '0'
kind,ij=CHART.split(':'); ij=[int(c) for c in ij.split(',')]
qv=['q%d'%i for i in range(7)]; qx={q:(q if k!=QC else '1') for k,q in enumerate(qv)}
if kind=='P':
    piv=ij; free=[c for c in range(10) if c not in piv]; gv=['g%d_%d'%(s,c) for s in range(2) for c in free]
    def coord(s,c):
        if c in piv: return '1' if piv.index(c)==s else '0'
        return 'g%d_%d'%(s,c)
    AB=[('x*(%s) + y*(%s)'%(coord(0,j),coord(1,j)),'x*(%s) + y*(%s)'%(coord(0,5+j),coord(1,5+j))) for j in range(5)]
else:
    I,J=ij; gv=['u%d'%j for j in range(5) if j!=I]+['p%d'%j for j in range(5) if j!=J]
    AB=[('x*(%s)'%('1' if j==I else 'u%d'%j),'y*(%s)'%('1' if j==J else 'p%d'%j)) for j in range(5)]
if SH=='a3': shape=['m0-m1','m1-m2']; rab='m0*m3*m4'
else:        shape=['m0-m1','m2-m3']; rab='m0*m2*m4'
pairs=[(0,1),(1,2)] if SH=='a3' else [(0,1),(2,3)]; codes=[SPL[0:2],SPL[2:4]]
unk=gv+['m0','m1','m2','m3','m4']+[q for k,q in enumerate(qv) if k!=QC]+['z','cc0','cc1']
L=['ring R = %s, (%s,x,y), dp;'%(CH,','.join(unk)),'option(redSB);']
for j in range(5): L.append('poly a%d = %s; poly b%d = %s;'%(j,AB[j][0],j,AB[j][1]))
L.append('''proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}
proc sm(list v){ poly s=0; int i; for(i=1;i<=size(v);i++){s=s+v[i];} return(s);}
proc dot(list v, list w){ poly s=0; int i; for(i=1;i<=size(v);i++){s=s+v[i]*w[i];} return(s);}
proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }
list A = a0,a1,a2,a3,a4; list B = b0,b1,b2,b3,b4; list M = m0,m1,m2,m3,m4;
ideal F;
proc addco(poly f){ matrix C = coef(f, x*y); int ii; for(ii=1;ii<=ncols(C);ii++){ F = F, C[2,ii]; } }
addco(3*(dot(A,B)-sm(A)*sm(B))); addco(6*(e3(A)+e3(B)));''')
L.append('poly Q2 = (%s)*x^2 + (%s)*x*y + (%s)*y^2; poly Q3 = (%s)*x^3 + (%s)*x^2*y + (%s)*x*y^2 + (%s)*y^3;'%tuple(qx[q] for q in qv))
L.append('''int k; for(k=1;k<=5;k++){ list Ak = dropk(A,k); list Bk = dropk(B,k);
  addco(3*(dot(Ak,Bk)-sm(Ak)*sm(Bk)) - M[k]*Q2); addco(6*(e3(Ak)+e3(Bk)) - M[k]*Q3); kill Ak; kill Bk; }
F = F, m0+m1+m2+m3+m4, %s, 1 - z*%s;'''%(', '.join(shape),rab))
L.append('poly hA = sm(A)/2; poly hB = sm(B)/2;')
for n,((i,j),cd) in enumerate(zip(pairs,codes)):
    c0,c1=('1','cc%d'%n) if cd[1]=='0' else ('cc%d'%n,'1')
    li,lj,mi,mj='(a%d-hA)'%i,'(a%d-hA)'%j,'(b%d-hB)'%i,'(b%d-hB)'%j
    if cd[0]=='S': e1,e2='(%s)*%s - (%s)*%s'%(c0,lj,c1,li),'(%s)*%s - (%s)*%s'%(c1,mj,c0,mi)
    else: e1,e2='(%s)*%s - (%s)*%s'%(c0,lj,c1,mi),'(%s)*%s - (%s)*%s'%(c1,mj,c0,li)
    L.append('addco(%s); addco(%s);'%(e1,e2))
L.append('F = simplify(F, 2+4+8);')
L.append('ring R2 = %s, (%s), dp; ideal F2 = imap(R, F); option(redSB);'%(CH,','.join(unk)))
L.append('int t0 = timer; ideal G = std(F2); int u = ((size(G)==1) && (deg(G[1])==0)); int vd = -2; if(u==0){ if(dim(G)==0){ vd = vdim(G); } write(":w %s.gb", G); }'%out[:-5])
L.append('"VERDICT", u, "DIM", dim(G), "VDIM", vd, "SECONDS", timer - t0;')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
