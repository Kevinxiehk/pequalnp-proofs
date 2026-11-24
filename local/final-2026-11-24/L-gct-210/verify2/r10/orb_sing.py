# verify2 r10: independent exact check of rows R8.9 (++++ / ----) with the expansion done INSIDE Singular (over Q). Same formulation as orb_indep.py.
import sys
out=sys.argv[1]
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
def conf(name):
    if name=='pppp': return 'matrix B0[3][3]=1/4*I3+1/4*hh+r/4*cx;', ['r2-5'.replace('r2','r^2')]
    if name=='mmmm': return 'matrix B0[3][3]=5/4*I3-3/4*hh-ii*r/4*cx;', ['r^2-3','ii^2+1']
for name in ('pppp','mmmm','cal3'):
    vars_='R0,R1,R2,R3,R4,R5,R6,R7,R8'+(',r' if name!='cal3' else '')+(',ii' if name=='mmmm' else '')
    L=['ring S=0,(u0,u1,u2,%s),dp;'%vars_,'option(redSB);',
       'matrix R[3][3]=R0,R1,R2,R3,R4,R5,R6,R7,R8; matrix I3[3][3]=1,0,0,0,1,0,0,0,1;',
       'matrix H[4][3]=%s;'%','.join(str(x) for row in H for x in row),
       'matrix tau[3][1]=u0,u1,u2; list cols; int j; int k; matrix h[3][1]; matrix hh[3][3]; matrix cx[3][3];']
    if name!='cal3':
        line,ex=conf(name)
        L.append('for(j=1;j<=4;j++){ h[1,1]=H[j,1]; h[2,1]=H[j,2]; h[3,1]=H[j,3]; hh=h*transpose(h); cx=0*I3; cx[1,2]=-h[3,1]; cx[1,3]=h[2,1]; cx[2,1]=h[3,1]; cx[2,3]=-h[1,1]; cx[3,1]=-h[2,1]; cx[3,2]=h[1,1]; '+line+' matrix A[3][3]=(I3-R*B0*transpose(R))/2; cols[j]=H*(A*tau); kill A; kill B0; }')
        n=4
    else:
        ex=[]
        L.append('for(j=1;j<=3;j++){ matrix P[3][3]; P[j,j]=1; matrix A[3][3]=R*P*transpose(R); cols[j]=H*(A*tau); kill A; kill P; }')
        n=3
    L.append('ideal E; matrix C; poly f; int a; int b; int c; int q;')
    L.append('for(a=1;a<=%d;a++){for(b=a+1;b<=%d;b++){for(c=b+1;c<=%d;c++){ f=0; for(q=1;q<=4;q++){ f=f+cols[a][q,1]*cols[b][q,1]*cols[c][q,1]; } C=coef(f,u0*u1*u2); for(k=1;k<=ncols(C);k++){ E=E,C[2,k]; } }}}'%(n,n,n))
    L.append('matrix O=transpose(R)*R-I3; for(a=1;a<=3;a++){for(b=a;b<=3;b++){ E=E,O[a,b]; }}')
    L.append('ring S2=0,(%s),dp; ideal E=imap(S,E); E=E,%s; ideal G=std(E);'%(vars_,','.join(ex) if ex else '0'))
    L.append('if (size(G)==1 and G[1]==1) {"RES %s UNIT";} else {"RES %s NONUNIT dim",dim(G);}'%(name,name))
    L.append('quit;')
    open('%s/orbS_%s.sing'%(out,name),'w').write('\n'.join(L)+'\n')
print('written')
