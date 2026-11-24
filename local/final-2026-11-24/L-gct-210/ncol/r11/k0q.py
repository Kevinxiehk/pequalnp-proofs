# CONJECTURE K0 over Q (big-slot driver input): 2-dim column-centred zero-row 3x5 level space S (Pluecker chart PIV of Gr(2,10) in
# isotropic coordinates a_0..a_4 = 0..4, b_0..b_4 = 5..9), defect d2_k = m_k Q2, d3_k = m_k Q3 (binary forms in x, y on S),
# e = 1 via the chart QC of (Q2, Q3) in P^6 (coefficient QC = 1), sum m = 0, and the OPEN condition prod_{j != I} m_j != 0
# (Rabinowitsch 1 - z prod).  K0 <=> every such system is UNIT over Q.  Exact identities (R2.5): P2 = 3(sum ab - AB), P3 = 6(e3 a + e3 b),
# d2_k = 3(sum_{j!=k} a_j b_j - A^(k) B^(k)), d3_k = 6(e3(a^(k)) + e3(b^(k))).
# usage: python3 -I k0q.py PIV(e.g. 0,5) QC(0..6) I(0..4 or -1 = no Rabinowitsch) OUT.sing [char]
import sys
piv=[int(c) for c in sys.argv[1].split(',')]; QC=int(sys.argv[2]); I=int(sys.argv[3]); out=sys.argv[4]; CH=sys.argv[5] if len(sys.argv)>5 else '0'
free=[c for c in range(10) if c not in piv]
gv=['g%d_%d'%(s,c) for s in range(2) for c in free]
qv=['q%d'%i for i in range(7)]
unk=gv+['m0','m1','m2','m3','m4']+[q for k,q in enumerate(qv) if k!=QC]+(['z'] if I>=0 else [])
def coord(s,c):
    if c in piv: return '1' if piv.index(c)==s else '0'
    return 'g%d_%d'%(s,c)
qx={q:(q if k!=QC else '1') for k,q in enumerate(qv)}
L=['ring R = %s, (%s,x,y), dp;'%(CH,','.join(unk)),'option(redSB);']
for j in range(5):
    L.append('poly a%d = x*(%s) + y*(%s); poly b%d = x*(%s) + y*(%s);'%(j,coord(0,j),coord(1,j),j,coord(0,5+j),coord(1,5+j)))
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
F = F, m0+m1+m2+m3+m4;''')
if I>=0:
    L.append('F = F, 1 - z*%s;'%('*'.join('m%d'%j for j in range(5) if j!=I)))
L.append('F = simplify(F, 2+4+8);')
L.append('ring R2 = %s, (%s), dp; ideal F2 = imap(R, F); option(redSB);'%(CH,','.join(unk)))
L.append('int t0 = timer; ideal G = std(F2); "VERDICT", ((size(G)==1) && (deg(G[1])==0)), "DIM", dim(G), "SECONDS", timer - t0;')
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
