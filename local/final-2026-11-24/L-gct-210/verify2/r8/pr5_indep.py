# verify2 r8: INDEPENDENT generator for rows' THEOREM PR5 computations (R7.4): types (3) and (2,1), N = {a m^T : a in A_N}.
#  m = (0, 1, mc, md, -1-mc-md) (columns a,b,c,d,e = 0..4); A_N in the 6 SCHUBERT cells of Gr(2,4) (rows used Pluecker charts);
#  type 3: K = {sigma e_0^T : sigma in V};  type 21: K = {(<x,x> sigma - <x,sigma> x) e_0^T + <x,sigma> x e_1^T}, x in V, chart x_k = 1,
#  u*<x,x> = 1 (over Q).  Equations: all coefficients of C_j - 24 - m_j (C_1 - 24), j != 1.  CAL: N a LINE (one vector a, 4 cells of P^3).
import sys, os, itertools
out=sys.argv[1]; cal=len(sys.argv)>2; os.makedirs(out,exist_ok=True)
sig=[['1','0','0','-1'],['0','1','0','-1'],['0','0','1','-1']]
def cells():
    if cal:
        for p in range(4): yield (p,)
    else:
        for p in itertools.combinations(range(4),2): yield p
for typ in ('3','21'):
    for piv in cells():
        for k in ((0,1,2) if typ=='21' else (None,)):
            unk=['mc','md']; rows=[]
            for r,pr in enumerate(piv):
                row=[]
                for c in range(4):
                    if c==pr: row.append('1')
                    elif c<pr or c in piv: row.append('0')
                    else: unk.append('a%d%d'%(r,c)); row.append('a%d%d'%(r,c))
                rows.append(row)
            if typ=='21':
                xv=['x%d'%i if i!=k else '1' for i in range(3)]; unk+=['x%d'%i for i in range(3) if i!=k]; xv.append('(-%s)'%'-'.join(xv)); unk.append('u')
            ids=['s1','s2','s3']+['t%d'%r for r in range(len(piv))]
            L=['ring R=0,(%s,%s),dp;'%(','.join(ids),','.join(unk))]
            L.append('proc p2(poly a,poly b,poly c,poly d){ return(a*d+b*c); }')
            L.append('proc p3(matrix M){ return(M[1,1]*p2(M[2,2],M[2,3],M[3,2],M[3,3])+M[1,2]*p2(M[2,1],M[2,3],M[3,1],M[3,3])+M[1,3]*p2(M[2,1],M[2,2],M[3,1],M[3,2])); }')
            L.append('proc p4(matrix M){ poly s=0; int c; int r; int q; int t; matrix S[3][3]; for(c=1;c<=4;c++){ for(r=2;r<=4;r++){ t=0; for(q=1;q<=4;q++){ if(q!=c){ t=t+1; S[r-1,t]=M[r,q]; } } } s=s+M[1,c]*p3(S); } return(s); }')
            L.append('list m=0,1,mc,md,-1-mc-md; matrix Y[4][5]; int i; int j; int k; poly xs; poly xx;')
            if typ=='21':
                L.append('matrix xv[4][1]=%s;'%','.join(xv)); L.append('xx=0; for(i=1;i<=4;i++){ xx=xx+xv[i,1]^2; }')
            for si,sv in enumerate(sig):
                L.append('matrix g%d[4][1]=%s;'%(si,','.join(sv)))
                if typ=='3':
                    L.append('for(i=1;i<=4;i++){ Y[i,1]=Y[i,1]+s%d*g%d[i,1]; }'%(si+1,si))
                else:
                    L.append('xs=0; for(i=1;i<=4;i++){ xs=xs+xv[i,1]*g%d[i,1]; }'%si)
                    L.append('for(i=1;i<=4;i++){ Y[i,1]=Y[i,1]+s%d*(xx*g%d[i,1]-xs*xv[i,1]); Y[i,2]=Y[i,2]+s%d*xs*xv[i,1]; }'%(si+1,si,si+1))
            for r,row in enumerate(rows):
                L.append('matrix av%d[4][1]=%s;'%(r,','.join(row)))
                L.append('for(i=1;i<=4;i++){ for(j=1;j<=5;j++){ Y[i,j]=Y[i,j]+t%d*av%d[i,1]*m[j]; } }'%(r,r))
            L.append('list C; matrix M[4][4]; int cc; poly F; matrix T;')
            L.append('for(j=1;j<=5;j++){ cc=0; for(k=1;k<=5;k++){ if(k!=j){ cc=cc+1; for(i=1;i<=4;i++){ M[i,cc]=1+Y[i,k]; } } } C[j]=p4(M)-24; }')
            L.append('ideal E; for(j=1;j<=5;j++){ if(j!=2){ F=C[j]-m[j]*C[2]; T=coef(F,%s); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; } } }'%'*'.join(ids))
            L.append('"NGEN",size(E);')
            L.append('ring R2=0,(%s),dp; ideal E=imap(R,E);'%','.join(unk))
            if typ=='21': L.append('poly xx=imap(R,xx); E=E,u*xx-1;')
            tag='%s_%s%s%s'%(typ,''.join(map(str,piv)),'_x%d'%k if k is not None else '','_CAL' if cal else '')
            L.append('ideal G=std(E); if (size(G)==1 and G[1]==1) {"RES %s UNIT";} else {"RES %s NONUNIT dim",dim(G),"size",size(G);}'%(tag,tag))
            L.append('quit;')
            open('%s/pr5_%s.sing'%(out,tag),'w').write('\n'.join(L)+'\n')
print('written')
