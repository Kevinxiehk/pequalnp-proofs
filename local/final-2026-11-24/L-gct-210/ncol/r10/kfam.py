# K_0-FAMILY systems (R10.6): K_0 a strongly level 2-dim zero-row space of family F1 or F2 (one homogeneous parameter [h0:h1]):
#   F1(a,b): span(nu1 (h0 e_a - h1 e_b)^T, nu2 (h0 e_a + h1 e_b)^T);  F2(a,b): span((h0 nu1 + h1 nu2) e_a^T, (h0 nu1 - h1 nu2) e_b^T).
# Y in P(V_0'/K_0) (two coordinates eliminated via K_0, chart HC: h0 = 1 [HC 0] or h1 = 1 [HC 1]), U_0 / C as in k0gen2 (TYPE a3|b22).
# usage: python3 -I kfam.py TYPE P FAM a b HC TC ZC OUT.ms
import sys
TY=sys.argv[1]; P=int(sys.argv[2]); FAM=sys.argv[3]; A_,B_=int(sys.argv[4]),int(sys.argv[5]); HC=int(sys.argv[6]); TC=int(sys.argv[7]); ZC=int(sys.argv[8]); out=sys.argv[9]
g=next(x for x in range(2,100) if pow(x,(P-1)//2,P)!=1 and pow(x,(P-1)//3,P)!=1); w=pow(g,(P-1)//3,P); i3=pow(3,P-2,P)
h0,h1=('1','hh') if HC==0 else ('hh','1')
# K_0 basis as dicts {('a'|'b', col): coeff-string}
if FAM=='F1':
    K=[{('a',A_):h0,('a',B_):'-(%s)'%h1},{('b',A_):h0,('b',B_):h1}]
    elim=[('a',A_),('b',A_)] if HC==0 else [('a',B_),('b',B_)]
else:
    K=[{('a',A_):h0,('b',A_):h1},{('a',B_):h0,('b',B_):'-(%s)'%h1}]
    elim=[('a',A_),('a',B_)] if HC==0 else [('b',A_),('b',B_)]
sg=['sg0','sg1','sg4'] if TY=='b22' else (['sg0','sg1','sg2'] if TY=='b23' else ['sg0','sg3','sg4'])
coords=sg+['a%d'%j for j in range(5) if ('a',j) not in elim]+['b%d'%j for j in range(5) if ('b',j) not in elim]
yx={c:(c if k!=ZC else '1') for k,c in enumerate(coords)}
def ya(j): return yx.get('a%d'%j,'0')
def yb(j): return yx.get('b%d'%j,'0')
unk=[c for k,c in enumerate(coords) if k!=ZC]+['hh']+(['tp'] if TC==0 else [])
L=['ring R = %d, (%s,k1,k2,yy,r1,r2), dp;'%(P,','.join(unk)),'short = 0;','poly w = %d; poly i3 = %d;'%(w,i3)]
pq=('1','tp') if TC==0 else ('0','1')
F1v,F2v=([1,1,0,0,-2],[0,0,1,1,-2]) if TY=='b22' else ([1,1,1,0,-3],[0,0,0,1,-1])
L.append('matrix tt[1][5] = %s;'%(','.join('(%s)*(%d)+(%s)*(%d)'%(pq[0],x1,pq[1],x2) for x1,x2 in zip(F1v,F2v))))
U2={'b22':'0,0,1,-1,0','a3':'0,1,-1,0,0','b23':('0,0,1,tp,-1-tp' if TC==0 else '0,0,0,1,-1')}[TY]
L.append('matrix one[1][5] = 1,1,1,1,1; matrix u1[1][5] = 1,-1,0,0,0; matrix u2[1][5] = %s;'%U2)
L.append('''matrix MM[4][5]; int j; for(j=1;j<=5;j++){ MM[1,j]=one[1,j]; MM[2,j]=u1[1,j]; MM[3,j]=u2[1,j]; MM[4,j]=tt[1,j]; }
matrix wp[1][5]; int c; int cc; int rr;
for(j=1;j<=5;j++){ matrix S4[4][4]; for(rr=1;rr<=4;rr++){ cc=0; for(c=1;c<=5;c++){ if(c!=j){ cc++; S4[rr,cc]=MM[rr,c]; } } } wp[1,j]=(-1)^j*det(S4); kill S4; }''')
if TY=='b23': L.append('wp[1,1]=3; wp[1,2]=3; wp[1,3]=-2; wp[1,4]=-2; wp[1,5]=-2;')   # C = V_01 + V_234 fixed
n1=['0','1','w','w^2']; n2=['0','1','w^2','w']; n0=['0','1','1','1']
def sval(l):
    if TY=='b23':   # U_0^perp = span(1, e0+e1, d3) with d3 = (0,0,-tp,1,0) [TC 0] or e2 [TC 2]
        d3={0:'0',1:'0',2:('-tp' if TC==0 else '1'),3:('1' if TC==0 else '0'),4:'0'}[l]
        return '(%s)'%yx['sg0']+('+(%s)'%yx['sg1'] if l in (0,1) else '')+'+(%s)*(%s)'%(yx['sg2'],d3)
    if TY=='b22': return '(%s)'%yx['sg0']+('+(%s)'%yx['sg1'] if l in (0,1) else '')+('+(%s)'%yx['sg4'] if l==4 else '')
    return '(%s)'%yx['sg0']+('+(%s)'%yx['sg3'] if l==3 else '')+('+(%s)'%yx['sg4'] if l==4 else '')
L.append('matrix Y[4][5];')
for r in range(4):
    for l in range(5):
        t=[]
        for kk,Kv in enumerate(K):
            if r>0:
                ca=Kv.get(('a',l)); cb=Kv.get(('b',l))
                if ca: t.append('k%d*(%s)*(%s)'%(kk+1,ca,n1[r]))
                if cb: t.append('k%d*(%s)*(%s)'%(kk+1,cb,n2[r]))
        if r==0: t.append('yy*(-(%s))'%sval(l)); t.append('r1*u1[1,%d] + r2*u2[1,%d]'%(l+1,l+1))
        else: t.append('yy*(i3*(%s)*(%s) + (%s)*(%s) + (%s)*(%s))'%(sval(l),n0[r],ya(l),n1[r],yb(l),n2[r]))
        L.append('Y[%d,%d] = %s;'%(r+1,l+1,' + '.join(t)))
L.append('''proc perm4(matrix A){ poly s = 0; int a; int b; int c; int d;
  for(a=1;a<=4;a++){ for(b=1;b<=4;b++){ if(b!=a){ for(c=1;c<=4;c++){ if(c!=a && c!=b){ d = 10-a-b-c;
    s = s + A[1,a]*A[2,b]*A[3,c]*A[4,d]; }}}}}
  return(s); }
proc delcol(matrix A, int k){ matrix B[4][4]; int r; int c; int cc; for(r=1;r<=4;r++){ cc=0; for(c=1;c<=5;c++){ if(c!=k){ cc++; B[r,cc]=1+A[r,c]; }}} return(B); }
poly S1 = 0; poly SW = 0; int k; poly Rk;
for(k=1;k<=5;k++){ Rk = perm4(delcol(Y,k))-24; S1 = S1 + Rk; SW = SW + Rk*wp[1,k]; }
ideal E;''')
for cnd in ('S1','SW'):
    L.append('matrix C = coef(%s, k1*k2*yy*r1*r2); int ii; for(ii=1;ii<=ncols(C);ii++){ if(C[2,ii]!=0){ E = E, C[2,ii]; } } kill C; kill ii;'%cnd)
L.append('E = simplify(E, 2+4+8); "NEQ", size(E);')
L.append('link lo = ":w %s"; open(lo); write(lo, "%s"); write(lo, "%d");'%(out,','.join(unk),P))
L.append('int q; for(q=1;q<=size(E);q++){ if(q<size(E)){ write(lo, string(E[q])+","); } else { write(lo, string(E[q])); } } close(lo);')
L.append('"WROTE"; quit;')
open(out.replace('.ms','.sing'),'w').write('\n'.join(L)+'\n')
