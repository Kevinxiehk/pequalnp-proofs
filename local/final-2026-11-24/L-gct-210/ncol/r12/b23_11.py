# b23 restricted (1,1) classification: S = span((a,0),(0,b)), e = 1, defect line m = (0,0,m2,m3,m4) with m2 m3 m4 != 0.
# Hand split as R11.14: CASE A (F == G == 0; |supp a|, |supp b| <= 2 by Lemma Z; m ~ D), CASE B (G == 0, F != 0: m ~ F, a_2 a_3 a_4 != 0,
# |supp b| <= 2), CASE C (F, G != 0: m ~ F, G = gam F, a_k, b_k != 0 for k = 2,3,4).  Rows 0, 1 of (D,F,G) vanish.
# usage: python3 -I b23_11.py CASE SPEC CH OUT.sing
#   CASE A: SPEC = "SA;SB" supports, e.g. "23;34" (a on {2,3}, b on {3,4}); normalisation: first support entry of a and of b = 1.
#   CASE B: SPEC = "I;SB": a_I = 1 (I in {2,3,4}), b support SB (|SB| <= 2), first entry of b = 1.
#   CASE C: SPEC = "I;J": a_I = 1, b_J = 1 (I, J in {2,3,4}).
import sys
CASE,SPEC,CH,out=sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4]; CODE=sys.argv[5] if len(sys.argv)>5 else ''; SPC=(len(sys.argv)>6 and sys.argv[6]=='spec')
# 'spec' = the special U_0 of b23 (t' ~ e_2 - e_3: zeros at 0, 1, 4)
s1,s2=SPEC.split(';')
def vec(name,supp,one):
    e=[];par=[]
    for k in range(5):
        if supp is not None and k not in supp: e.append('0')
        elif k==one: e.append('1')
        else: e.append(name+str(k)); par.append(name+str(k))
    return e,par
if CASE=='A':
    SA=[int(c) for c in s1]; SB=[int(c) for c in s2]; a,pa=vec('a',SA,SA[0]); b,pb=vec('b',SB,SB[0])
elif CASE=='B':
    I=int(s1); SB=[int(c) for c in s2]; a,pa=vec('a',None,I); b,pb=vec('b',SB,SB[0])
else:
    I,J=int(s1),int(s2); a,pa=vec('a',None,I); b,pb=vec('b',None,J)
par=pa+pb+['del','gam','z']
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'ring R = %s, (%s), dp; option(redSB);'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(a),','.join(b)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'list D; list F; list G; for(k=1;k<=5;k++){ D = insert(D, SA*B[k]+SB*A[k]-2*A[k]*B[k], size(D)); F = insert(F, A[k]*e2(dropk(A,k)), size(F)); G = insert(G, B[k]*e2(dropk(B,k)), size(G)); }',
'ideal I0 = e3(A), e3(B), ab - SA*SB;']
if CASE=='A':   # m := D; F = G = 0 automatically (supports <= 2); D_0 = D_1 = 0; D_2 D_3 D_4 != 0
    L.append('I0 = I0, D[1], D[2], 1 - z*D[3]*D[4]*D[5], del, gam;' if not SPC else 'I0 = I0, D[1], D[2], D[5], 1 - z*D[3], del, gam;')
elif CASE=='B': # m := F; D = del F; F_0 = F_1 = 0 (=> D_0 = D_1 = 0); F_2 F_3 F_4 != 0; G = 0 automatically
    L.append('for(k=1;k<=5;k++){ I0 = I0, D[k] - del*F[k]; } I0 = I0, F[1], F[2], 1 - z*F[3]*F[4]*F[5], gam;' if not SPC else 'for(k=1;k<=5;k++){ I0 = I0, D[k] - del*F[k]; } I0 = I0, F[1], F[2], F[5], 1 - z*F[3], gam;')
elif CODE=='':  # m := F; D = del F, G = gam F, gam != 0
    L.append('for(k=1;k<=5;k++){ I0 = I0, D[k] - del*F[k], G[k] - gam*F[k]; } I0 = I0, F[1], F[2], 1 - z*gam*F[3]*F[4]*F[5];' if not SPC else 'for(k=1;k<=5;k++){ I0 = I0, D[k] - del*F[k], G[k] - gam*F[k]; } I0 = I0, F[1], F[2], F[5], 1 - z*gam*F[3];')
else:           # split: F_0 = a_0 h_a(a_0), F_1, G_0, G_1 replaced by one factor each (CODE letters for F0,F1,G0,G1: Z = linear, H = quadric)
    def fac(V,S,k,c): return '%s[%d]'%(V,k+1) if c=='Z' else '(%s[%d]^2 - %s*%s[%d] + e2(%s))'%(V,k+1,S,V,k+1,V)
    eq=[fac('A','SA',0,CODE[0]),fac('A','SA',1,CODE[1]),fac('B','SB',0,CODE[2]),fac('B','SB',1,CODE[3])]
    L.append('for(k=1;k<=5;k++){ I0 = I0, D[k] - del*F[k], G[k] - gam*F[k]; } I0 = I0, %s, %s;'%(', '.join(eq), '1 - z*gam*F[3]*F[4]*F[5]' if not SPC else 'F[5], 1 - z*gam*F[3]'))
L+=['int t0 = timer; ideal Gb = std(I0); "STD", "%s %s %s", "unit", ((size(Gb)==1) && (deg(Gb[1])==0)), "dim", dim(Gb), "SECONDS", timer - t0;'%(CASE,SPEC,CODE),
'if(!((size(Gb)==1) && (deg(Gb[1])==0))){ list pr = minAssGTZ(Gb); "NCOMP", size(pr); int q;',
'  for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); "COMP", q, "dim", dim(P); P; kill P; } }',
'quit;']
open(out,'w').write('\n'.join(L)+'\n')
