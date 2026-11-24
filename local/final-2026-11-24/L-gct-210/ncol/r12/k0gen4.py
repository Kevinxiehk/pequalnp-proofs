# K_0-FIXED admissible-Y system for an EXPLICIT e = 1 member K_0 = span((al1, be1), (al2, be2)) (isotropic coordinates, zero row,
# column-centred), types a3 / b22 (as ncol/r10/k0gen2.py, whose rigid-pair K_0 this replaces).  Entries of K_0 are computed mod P in Python
# (members over Q(sqrt D) use a fixed square root mod P).  Unknowns: Y in P(V_0'/K_0) (11 coords, chart ZC), tp (C = U_0 + C(F1 + tp F2),
# TC 0) -- tp is forced by K_0's own defect line.  Output (Singular, mod P): KCAL = the ideal in tp of the K_0-only equations
# (calibration: must be tp - tp0), then VERDICT (unit), DIM, VDIM of the admissible set in this chart.
# k0gen4: TYPE b23 with a PARAMETRIC member (family A23: a = (0,0,a2,a3,0), b = (0,0,0,b3,b4), a2(b3+b4) + a3 b4 = 0),
# member chart MC in {0..3}: (a2 = 1 | a3 = 1) x (b3 = 1 | b4 = 1); parameters hh (free a-coordinate), bb (free b-coordinate), tp.
# Output: KCAL (K_0-only equations), VERDICT/DIM, and FIBRES_FINITE (block order Y > params: every Y variable has a pure-power
# leading monomial => admissible Y finite for every parameter value).
# usage: python3 -I k0gen4.py MC TC ZC OUT.sing [P]
import sys
MC=int(sys.argv[1]); MEM='b23_A23'; TC=int(sys.argv[2]); ZC=int(sys.argv[3]); out=sys.argv[4]; P=int(sys.argv[5]) if len(sys.argv)>5 else 65521
def sqrtm(a):
    a%=P
    for x in range(P):
        if x*x%P==a: return x
inv=lambda x: pow(x%P,P-2,P)
def member(name):
    # returns TY, al1, be1, al2, be2 (lists of ints mod P), ia, ib (Y's a/b index eliminated by K_0)
    z=[0]*5; b=[1,P-1,0,0,0]
    if name=='a3_rig0123': return 'a3',[1,P-1,0,0,0],z,z,[0,0,1,P-1,0]   # calibration (R9.6: NONUNIT at tp = -3)
    if name=='b22_rat': return 'b22',[1,1,P-3,P-3,6],z,z,b
    if name in ('b22_39p','b22_39m'):
        r=sqrtm(-39); r=r if name.endswith('p') else P-r
        d=(3+r)*inv(12)%P; c=(inv(2)-d)%P; return 'b22',[1,1,c,d,(P-c-d-2)%P if False else (-1-c-d)%P],z,z,b
    if name in ('a3_15p','a3_15m'):
        r=sqrtm(-15); r=r if name.endswith('p') else P-r
        d=(-3+r)*inv(6)%P; return 'a3',[1,1,1,d,(-1-1-d+1)%P if False else (-2-d+1)%P],z,z,b
    if name in ('a3_ip','a3_im'):
        r=sqrtm(-1); r=r if name.endswith('p') else P-r
        d=(-1+r)%P; return 'a3',[1,1,2,d,(-2-d)%P],z,z,b
TY='b23'
ach,bch=MC//2,MC%2
SPECIAL=(MC>=10)   # special U_0 of b23: v = (0,0,1,1,-2) (tp = 1), t' ~ e2 - e3; members a in span(e_i,e_j), {i,j} in {0,1,4}, b = e2 - e3
if MC==9: ach,bch=9,9
if SPECIAL: ach,bch=MC,9   # calibration: rigid pair (01|23), R11.5 found NONUNIT finite charts
if ach==10: av=['1','hh','0','0','0']; ia=0
elif ach==11: av=['hh','1','0','0','0']; ia=1
elif ach==12: av=['1','0','0','0','hh']; ia=0
elif ach==13: av=['hh','0','0','0','1']; ia=4
elif ach==9: av=['1','-1','0','0','0']; ia=0
elif ach==0: av=['0','0','1','hh','0']; ia=2
else:      av=['0','0','hh','1','0']; ia=3
if bch==9: bv=['0','0','1','-1','0']; ib=2
elif bch==0: bv=['0','0','0','1','bb']; ib=3
else:      bv=['0','0','0','bb','1']; ib=4
rel='(%s)*((%s)+(%s)) + (%s)*(%s)'%(av[2],bv[3],bv[4],av[3],bv[4]) if (MC!=9 and not SPECIAL) else ('tp-1' if (SPECIAL and TC==0) else ('1' if SPECIAL else '0'))
al1,be1,al2,be2=av,['0']*5,['0']*5,bv
g=next(x for x in range(2,100) if pow(x,(P-1)//2,P)!=1 and pow(x,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=inv(3)
coords=['sg0','sg1','sg2']+['a%d'%j for j in range(5) if j!=ia]+['b%d'%j for j in range(5) if j!=ib]
yx={c:(c if k!=ZC else '1') for k,c in enumerate(coords)}
def ya(j): return yx.get('a%d'%j,'0')
def yb(j): return yx.get('b%d'%j,'0')
yv=[c for k,c in enumerate(coords) if k!=ZC]; pv=['hh','bb']+(['tp'] if TC==0 else []); unk=yv+pv
L=['ring R = %d, (%s,k1,k2,yy,r1,r2), dp;'%(P,','.join(unk)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
pq=('1','tp') if TC==0 else ('0','1')
F1,F2=([1,1,0,0,-2],[0,0,1,1,-2]) if TY=='b22' else ([1,1,1,0,-3],[0,0,0,1,-1])
L.append('matrix tt[1][5] = %s;'%(','.join('(%s)*(%d)+(%s)*(%d)'%(pq[0],f1,pq[1],f2) for f1,f2 in zip(F1,F2))))
U2=('0,0,1,tp,-1-tp' if TC==0 else '0,0,0,1,-1')
L.append('matrix one[1][5] = 1,1,1,1,1; matrix u1[1][5] = 1,-1,0,0,0; matrix u2[1][5] = %s;'%U2)
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=u1[1,j]; MM[3,j]=u2[1,j]; MM[4,j]=tt[1,j]; }
matrix wp[1][5] = 3,3,-2,-2,-2; int c; int cc; int rr;''')
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def sval(l):
    d3={0:'0',1:'0',2:('-tp' if TC==0 else '1'),3:('1' if TC==0 else '0'),4:'0'}[l]
    return '(%s)'%yx['sg0']+('+(%s)'%yx['sg1'] if l in (0,1) else '')+'+(%s)*(%s)'%(yx['sg2'],d3)
    if TY=='b22': return '(%s)'%yx['sg0']+('+(%s)'%yx['sg1'] if l in (0,1) else '')+('+(%s)'%yx['sg4'] if l==4 else '')
    return '(%s)'%yx['sg0']+('+(%s)'%yx['sg3'] if l==3 else '')+('+(%s)'%yx['sg4'] if l==4 else '')
L.append('matrix Y[4][5];')
for r in range(4):
    for l in range(5):
        t=[]
        if r>0:
            t.append('k1*((%s)*(%s) + (%s)*(%s))'%(al1[l],n1[r],be1[l],n2[r]))
            t.append('k2*((%s)*(%s) + (%s)*(%s))'%(al2[l],n1[r],be2[l],n2[r]))
            t.append('yy*(i3*(%s)*(%s) + (%s)*(%s) + (%s)*(%s))'%(sval(l),n0[r],ya(l),n1[r],yb(l),n2[r]))
        else: t.append('yy*(-(%s))'%sval(l)); t.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
        L.append('Y[%d,%d] = %s;'%(r+1,l+1,' + '.join(t)))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
poly S1 = 0; poly SW = 0; int k; poly Rk;
for(k=1;k<=5;k++){ Rk = perm4(delcol(Y,k))-24; S1 = S1 + Rk; SW = SW + Rk*wp[1,k]; }
ideal E; ideal EK;''')
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, k1*k2*yy*r1*r2); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; if(subst(subst(subst(C[1,ii],k1,1),k2,1),r1,1)==C[1,ii]){} if(diff(C[1,ii],yy)==0 && diff(C[1,ii],r1)==0 && diff(C[1,ii],r2)==0){ EK = EK, C[2,ii]; } } } kill C; kill ii;'%cnd)
L.append('E = simplify(E, 2+4+8); EK = simplify(EK, 2+4+8);')
L.append('E = E, %s; EK = EK, %s;'%(rel,rel))
L.append('ring R2 = %d, (%s), (dp(%d),dp(%d)); option(redSB); ideal E2 = imap(R, E); ideal EK2 = imap(R, EK);'%(P,','.join(unk),len(yv),len(pv)))
L.append('"KCAL", std(EK2);')
L.append('int t0 = timer; ideal G = std(E2); int u = ((size(G)==1) && (deg(G[1])==0)); int vd = -2; if(u==0 && dim(G)==0){ vd = vdim(G); }')
L.append('"VERDICT", u, "DIM", dim(G), "VDIM", vd, "SECONDS", timer - t0;')
L.append('int ok = 1; int i; int jj; int found; poly lm; for(i=1;i<=%d;i++){ found=0; for(jj=1;jj<=size(G);jj++){ lm = leadmonom(G[jj]); if (lm == var(i)^deg(lm)) { found=1; } } if(found==0){ ok=0; } } "FIBRES_FINITE", ok;'%len(yv))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
print(TY,'a',al1,'b',be2,'ia',ia,'ib',ib,'rel',rel,'coords',coords)
