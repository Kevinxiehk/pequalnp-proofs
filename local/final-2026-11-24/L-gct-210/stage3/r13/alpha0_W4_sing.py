# Singular-native version of alpha0_W4: Singular builds the matrix over Q(i), expands the 4x4 permanents, extracts coefficients w.r.t.
# the parameters (t, s1, s2, s3, mu) with coef(), then std over Q(i).
import itertools
I='I'
lines=[]
def conjdot(v,w):
    m={'1':1,'I':1j,'-1':-1,'-I':-1j}; return sum((m[a].conjugate())*m[b] for a,b in zip(v,w))
for p in itertools.permutations(range(4)):
    v=[ ['1','I','-1','-I'][k] for k in p ]
    if not any(abs(conjdot(v,w))>3.9 for w in lines): lines.append(v)
combo=(0,1,4,5); lam=['(-1)','(1)','(I)','(-I)']
W=[['(%s)*(%s)'%(lam[j],lines[combo[j]][r]) for j in range(4)] for r in range(4)]
fv=['f%d_%d'%(k,i) for k in (1,2,3) for i in range(3)]
out=['ring R=(0,I),(%s,t,s1,s2,s3,mu),dp;'%','.join(fv),'minpoly=I^2+1;']
out.append('poly s0=s1; poly sv1=s2-s1; poly sv2=s3-s2; poly sv3=-s3;')
out.append('matrix S[4][1]=s0,sv1,sv2,sv3;')
out.append('matrix F[4][4];')     # F[k+1][r+1] = phi_k entry r (phi_0 = 0)
for k in (1,2,3):
    out.append('F[%d][1]=f%d_0; F[%d][2]=f%d_1; F[%d][3]=f%d_2; F[%d][4]=-(f%d_0+f%d_1+f%d_2);'%((k+1,k)*3+(k+1,k,k,k)))
out.append('matrix Wm[4][4];')
for r in range(4):
    for j in range(4): out.append('Wm[%d][%d]=%s;'%(r+1,j+1,W[r][j]))
Sv=['s1','(s2-s1)','(s3-s2)','(-s3)']
F={0:['0','0','0','0']}
for k in (1,2,3): F[k]=['f%d_0'%k,'f%d_1'%k,'f%d_2'%k,'(-(f%d_0+f%d_1+f%d_2))'%(k,k,k)]
cc={j:'('+'+'.join('%s*%s'%(F[j][r],Sv[r]) for r in range(4))+')' for j in range(4)}
out.append('matrix Y[4][5];')
for r in range(4):
    for j in range(4): out.append('Y[%d][%d]=(%s+%s*%s)/2+mu*%s;'%(r+1,j+1,Sv[r],cc[j],W[r][j],W[r][j]))
    out.append('Y[%d][5]=-%s-('%(r+1,Sv[r])+'+'.join('%s*%s'%(cc[j],W[r][j]) for j in range(4))+')/2;')
out.append('int j;')
perms=list(itertools.permutations(range(4)))
def permexpr(cols):
    terms=[]
    for p in perms:
        terms.append('*'.join('(1+t*Y[%d][%d])'%(r+1,cols[p[r]]+1) for r in range(4)))
    return '+'.join(terms)
for jdel in range(5):
    cols=[x for x in range(5) if x!=jdel]; out.append('poly C%d=%s;'%(jdel,permexpr(cols)))
out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120;')
out.append('ideal J; int k; matrix M; for(k=1;k<=4;k++){ M=coef(D[k],t*s1*s2*s3*mu); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} }')
out.append('J=simplify(J,2); "equations",size(J);')
out.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal J=imap(R,J); ideal G=std(J); "ALPHA0 W4 RESULT size",size(G),"dim",dim(G); if(size(G)<=6){G;}'%','.join(fv))
out.append('quit;')
open('/home/kevxhk/work/L-gct-210/stage3/r13/alpha0_W4n.sing','w').write('\n'.join(out)+'\n'); print('written')
