# verify2 r11: independent generator for stage3 Lemma S-SPEC (33(E)). Y = a (x) (1,1,1,1,-2)^T + b (x) (e_k - e_4)^T, k = 3 WLOG (S_4 on columns 0..3).
# Line C Y has defect in C m0  <=>  all t-coefficients of perm(J4 + t Y^(j)) - 24 - lam_t * m0_j vanish, eliminated as: C_j = C_0 (j=1,2,3), C_4 + 4 C_0 = 120.
# My own permanent expansion (explicit sum over S_4) printed directly into Singular; t handled as a ring variable and coefficients taken by coeffs().
import itertools
P4=list(itertools.permutations(range(4)))
def ent(r,c):  # entry of J4 + t Y at row r, column c (5 columns), Y_rc = a_r m_c + b_r e_c
    m=[1,1,1,1,-2][c]; e=[0,0,0,1,-1][c]
    return '(1+t*(%s*(%d)+%s*(%d)))'%('a%d'%r,m,'b%d'%r,e)
def perm_del(j):
    cols=[c for c in range(5) if c!=j]
    return '+'.join('*'.join(ent(r,cols[p[r]]) for r in range(4)) for p in P4)
for chart in range(3):
    L=['ring R=0,(t,a0,a1,a2,a3,b0,b1,b2,b3,u),dp;']
    for j in range(5): L.append('poly C%d=%s;'%(j,perm_del(j)))
    L.append('ideal D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal E;')
    L.append('int k; matrix cf; for(k=1;k<=4;k++){ cf=coeffs(D[k],t); E=E+ideal(cf); }')
    L.append('E=E,a0+a1+a2+a3,b0+b1+b2+b3,b0^2+b1^2+b2^2+b3^2,a%d-1;'%chart)
    L.append('ring S=0,(a0,a1,a2,a3,b0,b1,b2,b3),dp; ideal E=imap(R,E); option(redSB); ideal G=std(E); ideal G3=std(G+ideal(b0^3+b1^3+b2^3+b3^3)); printf("   no-u ring: line conditions dim %%s vdim %%s; with p3(b)=0: vdim %%s",dim(G),vdim(G),vdim(G3)); ring S2=0,(a0,a1,a2,a3,b0,b1,b2,b3,u),dp; ideal G=imap(S,G);')
    L.append('printf("chart a%d=1: line conditions dim %%s vdim %%s",dim(G),vdim(G));'%chart)
    L.append('ideal H=std(G+ideal(1-u*(b0^3+b1^3+b2^3+b3^3))); printf("chart a%d=1: + (p3(b) != 0): unit %%s",reduce(1,H)==0);'%chart)
    L.append('ideal H2=std(G+ideal(b0^3+b1^3+b2^3+b3^3)); printf("   calibration: + p3(b) = 0: dim %%s vdim %%s",dim(H2),vdim(H2));')
    L.append('quit;')
    open('shapeS_mine_%d.sing'%chart,'w').write('\n'.join(L)+'\n')
print('written')
