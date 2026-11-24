# Generalised rank-minor system (no m/Q variables) for 2-dim zero-row column-centred level spaces S = {(a(x,y), b(x,y))}:
#   P2 == 0, P3 == 0, rank <= 1 of the 5x7 matrix W (row k = coefficients of d2_k, d3_k), rows in ZR forced to 0.
# SUB 11: a = x*u (u_I = 1), b = y*p (p_J = 1).
# SUB 21: a = x*u + y*v (v_I = 1, u_I = 0), b = x*p (p_J = 1).      [b-projection rank 1]
# SUB 22: a = x*u + y*v with pivots (I,J): u_I = 1, u_J = 0, v_I = 0, v_J = 1; b = x*p + y*q (free).   [a-projection rank 2]
# usage: python3 -I k0rk2.py SUB I J CH ZR(e.g. 01 or -) OUT.sing [MODE: dec|dim]
import sys
SUB,I,J,CH,ZR,out=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],sys.argv[5],sys.argv[6]; MODE=sys.argv[7] if len(sys.argv)>7 else 'dec'
zr=[] if ZR=='-' else [int(c) for c in ZR]
def vec(name,fix):
    e=[];par=[]
    for i in range(5):
        if i in fix: e.append(fix[i])
        else: e.append(name+str(i)); par.append(name+str(i))
    return e,par
if SUB=='11':
    u,pu=vec('u',{I:'1'}); p,pp=vec('p',{J:'1'}); par=pu+pp
    A=['x*(%s)'%u[i] for i in range(5)]; B=['y*(%s)'%p[i] for i in range(5)]
elif SUB=='21':
    u,pu=vec('u',{I:'0'}); v,pv=vec('v',{I:'1'}); p,pp=vec('p',{J:'1'}); par=pu+pv+pp
    A=['x*(%s)+y*(%s)'%(u[i],v[i]) for i in range(5)]; B=['x*(%s)'%p[i] for i in range(5)]
elif SUB=='22':
    u,pu=vec('u',{I:'1',J:'0'}); v,pv=vec('v',{I:'0',J:'1'}); p,pp=vec('p',{}); q,pq=vec('q',{}); par=pu+pv+pp+pq
    A=['x*(%s)+y*(%s)'%(u[i],v[i]) for i in range(5)]; B=['x*(%s)+y*(%s)'%(p[i],q[i]) for i in range(5)]
L=['LIB "primdec.lib";',
'proc e2(list v){ poly s=0; int i; int j; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){s=s+v[i]*v[j];}} return(s);}',
'proc e3(list v){ poly s=0; int i; int j; int k; for(i=1;i<=size(v);i++){for(j=i+1;j<=size(v);j++){for(k=j+1;k<=size(v);k++){s=s+v[i]*v[j]*v[k];}}} return(s);}',
'proc dropk(list v, int k){ list w; int i; for(i=1;i<=size(v);i++){ if(i!=k){ w=insert(w,v[i],size(w)); } } return(w); }',
'proc cf(poly f, poly m){ matrix C = coef(f, x*y); int t; for(t=1;t<=ncols(C);t++){ if(C[1,t]==m){ return(C[2,t]); } } return(poly(0)); }',
'ring R = %s, (%s,x,y), dp;'%(CH,','.join(par)),
'list A = %s; list B = %s;'%(','.join(A),','.join(B)),
'poly SA = 0; poly SB = 0; poly ab = 0; int k; for(k=1;k<=5;k++){ SA = SA + A[k]; SB = SB + B[k]; ab = ab + A[k]*B[k]; }',
'poly P2 = ab - SA*SB; poly P3 = e3(A) + e3(B);',
'list m2 = x^2, x*y, y^2; list m3 = x^3, x^2*y, x*y^2, y^3; ideal I0; int t;',
'for(t=1;t<=3;t++){ I0 = I0, cf(P2, m2[t]); } for(t=1;t<=4;t++){ I0 = I0, cf(P3, m3[t]); }',
'matrix W[5][7];',
'for(k=1;k<=5;k++){ poly d2 = SA*B[k] + SB*A[k] - 2*A[k]*B[k]; poly d3 = A[k]*e2(dropk(A,k)) + B[k]*e2(dropk(B,k));',
'  for(t=1;t<=3;t++){ W[k,t] = cf(d2, m2[t]); } for(t=1;t<=4;t++){ W[k,3+t] = cf(d3, m3[t]); } kill d2; kill d3; }',
'I0 = I0 + minor(W,2);']
for z in zr: L.append('for(t=1;t<=7;t++){ I0 = I0, W[%d,t]; }'%(z+1))
L+=['ring S = %s, (%s), dp; ideal I = imap(R, I0); matrix Ws = imap(R, W);'%(CH,','.join(par))]
if MODE=='dim':
    L+=['int t0 = timer; ideal G = std(I); "DIM", dim(G), "SECONDS", timer - t0;']
else:
    L+=['int t0 = timer; list pr = minAssGTZ(I); "NCOMP", size(pr), "SECONDS", timer - t0;',
'int q; int z; int r;',
'for(q=1;q<=size(pr);q++){ ideal P = std(pr[q]); string zs = ""; int allz = 1;',
'  for(z=1;z<=5;z++){ int cz = 1; for(r=1;r<=7;r++){ if(reduce(Ws[z,r],P)!=0){ cz = 0; allz = 0; } } if(cz==1){ zs = zs + string(z-1) + " "; } kill cz; }',
'  "COMP", q, "dim", dim(P), " zeros of m:", zs, " e=0:", allz; if(allz == 0){ "  GENS", P; } kill P; kill zs; kill allz; }']
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n')
