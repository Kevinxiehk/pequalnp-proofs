# verify2 r10: [T31] split A over Q(i) (repair of the RED-p stratum caveat for verifyfl K1). verifyfl R8.2 normal form (char 0 hand reduction):
# Z = chi_1 l^T, chi_1 = (1,i,-1,-i), l = (1,t,-1-t,0,0) (l_0 = 1 after scaling; zero entries of l are excluded by hand for distinct entries of m);
# Y_r = b_r e_0^T + D(c_r) (r = 1,2; b_1 = (1,-1,0,0), b_2 = (0,1,-1,0)), gauge D(c_r)[0,0] = 0 (Z has entry 1 at (0,0)).  Stage a: span(Z, Y_1, Y_2).
# Equations: all (x0,x1,x2)-coefficients of <w, C(Y) - 24> for w in a basis of m^perp; ring over Q with ii (ii^2+1) [and w (w^2+w+1)].
import sys
mspec=sys.argv[1]; out=sys.argv[2]
if mspec=='m12m3': m=['1','2','(-3)','0','0']; W=[['2','-1','0','0','0'],['3','0','1','0','0'],['0','0','0','1','0'],['0','0','0','0','1']]; extra=[]; ev=[]
elif mspec=='iso': m=['1','w','w^2','0','0']; W=[['w','-1','0','0','0'],['w^2','0','-1','0','0'],['0','0','0','1','0'],['0','0','0','0','1']]; extra=['w^2+w+1']; ev=['w']
chi=['1','ii','(-1)','(-ii)']; l=['1','t','(-1-t)','0','0']
def D(pre):
    M=[['0']*5 for _ in range(4)]; vs=[]
    for a in range(3):
        for q in range(4):
            if (a,q)==(0,0): M[a][q]='0'; continue
            v='%s%d%d'%(pre,a,q); vs.append(v); M[a][q]=v
        M[a][4]='(-(%s))'%'+'.join(M[a][q] for q in range(4))
    for q in range(5): M[3][q]='(-(%s))'%'+'.join(M[a][q] for a in range(3))
    return M,vs
Y1,v1=D('c'); Y2,v2=D('d')
b=[['1','-1','0','0'],['0','1','-1','0']]
X=[['(%s*%s)'%(chi[a],l[q]) for q in range(5)] for a in range(4)]
Ym=[[ '(x0*%s+x1*(%s%s)+x2*(%s%s))'%(X[a][q], Y1[a][q], ('+'+b[0][a]) if q==0 else '', Y2[a][q], ('+'+b[1][a]) if q==0 else '') for q in range(5)] for a in range(4)]
unk=['t','ii']+ev+v1+v2
L=['ring R=0,(x0,x1,x2,%s),dp;'%','.join(unk),
   'proc p2(poly a,poly b,poly c,poly d){ return(a*d+b*c); }',
   'proc p3(matrix M){ return(M[1,1]*p2(M[2,2],M[2,3],M[3,2],M[3,3])+M[1,2]*p2(M[2,1],M[2,3],M[3,1],M[3,3])+M[1,3]*p2(M[2,1],M[2,2],M[3,1],M[3,2])); }',
   'proc p4(matrix M){ poly s=0; int c; int r; int q; int t; matrix S[3][3]; for(c=1;c<=4;c++){ for(r=2;r<=4;r++){ t=0; for(q=1;q<=4;q++){ if(q!=c){ t=t+1; S[r-1,t]=M[r,q]; } } } s=s+M[1,c]*p3(S); } return(s); }',
   'matrix Y[4][5]=%s;'%','.join(Ym[a][q] for a in range(4) for q in range(5)),
   'list C; matrix M[4][4]; int cc; int i; int j; int k; for(j=1;j<=5;j++){ cc=0; for(k=1;k<=5;k++){ if(k!=j){ cc=cc+1; for(i=1;i<=4;i++){ M[i,cc]=1+Y[i,k]; } } } C[j]=p4(M)-24; }',
   'ideal E; poly F; matrix T;']
for w in W:
    L.append('F=%s; T=coef(F,x0*x1*x2); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; }'%'+'.join('(%s)*C[%d]'%(w[j],j+1) for j in range(5) if w[j]!='0'))
L+=['ring R2=0,(%s),dp; ideal E=imap(R,E); E=E,ii^2+1%s; ideal G=std(E);'%(','.join(unk),''.join(','+e for e in extra)),
    'if (size(G)==1 and G[1]==1) {"RES %s UNIT";} else {"RES %s NONUNIT dim",dim(G);}'%(mspec,mspec),'quit;']
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
