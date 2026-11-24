# verify2 r8: INDEPENDENT generator for rows' THEOREM X5 (R7.3), different formulation from rows/r7/x5/x5gen.py:
#  isotropic lines n, n' in charts 'ab' (x_0 = 1, quadric) or 'z' (x = (0,1,w,w^2), w^2+w+1 = 0);  v in V with <v,n> = <v,n'> = 0 and a chart
#  v_k = 1 (k = 0,1,2);  <n,n'> != 0 by a Rabinowitsch variable (over Q: legitimate);  Singular's matrix.lib permanent.
#  K = span{ v e_c^T, n((1-lam)e_a+(1+lam)e_b)^T, n'((1-mu)e_a+(1+mu)e_b)^T },  lam*mu = 1;  m = (1, mb, 0, md, -1-mb-md), lam(1-mb) = 1+mb;
#  N = { A m^T + (lam-1) eta n (e_a - e_b)^T },  A = (kc phi/4) 1 + phi v + eta n,  kc^2 = (4/3)<v,v>   (normal form re-derived by verify2).
#  CAL: eta = r*phi (a line instead of the plane N) -> must be NON-unit somewhere.
# usage: python3 -I x5_indep.py OUTDIR [cal]
import sys, os, itertools
out=sys.argv[1]; cal=len(sys.argv)>2; os.makedirs(out,exist_ok=True)
def vec(ch,tag):
    if ch=='ab': return ['1','%sa'%tag,'%sb'%tag,'(-1-%sa-%sb)'%(tag,tag)], ['%sa'%tag,'%sb'%tag], '1+%sa^2+%sb^2+(1+%sa+%sb)^2'%((tag,)*4)
    return ['0','1','%sw'%tag,'%sw^2'%tag], ['%sw'%tag], '%sw^2+%sw+1'%(tag,tag)
for cn,cp,k in itertools.product(('ab','z'),('ab','z'),(0,1,2)):
    n,nv,qn=vec(cn,'n'); q,qv,qq=vec(cp,'q')
    vvars=['v%d'%i for i in range(4) if i!=k]; v=['v%d'%i if i!=k else '1' for i in range(4)]
    unk=nv+qv+vvars+['lam','mu','mb','md','kc','u']+(['rr'] if cal else [])
    ip=lambda x,y: '+'.join('(%s)*(%s)'%(a,b) for a,b in zip(x,y))
    L=['ring R=0,(s1,s2,s3,ph,et,%s),dp;'%','.join(unk)]
    L.append('proc p2(poly a,poly b,poly c,poly d){ return(a*d+b*c); }')
    L.append('proc p3(matrix M){ return(M[1,1]*p2(M[2,2],M[2,3],M[3,2],M[3,3])+M[1,2]*p2(M[2,1],M[2,3],M[3,1],M[3,3])+M[1,3]*p2(M[2,1],M[2,2],M[3,1],M[3,2])); }')
    L.append('proc p4(matrix M){ poly s=0; int c; int r; int q; int t; matrix S[3][3]; for(c=1;c<=4;c++){ for(r=2;r<=4;r++){ t=0; for(q=1;q<=4;q++){ if(q!=c){ t=t+1; S[r-1,t]=M[r,q]; } } } s=s+M[1,c]*p3(S); } return(s); }')
    L.append('list m=1,mb,0,md,-1-mb-md;')
    L.append('poly ETA=%s;'%('rr*ph' if cal else 'et'))
    L.append('matrix nn[4][1]=%s; matrix qv[4][1]=%s; matrix vv[4][1]=%s;'%(','.join(n),','.join(q),','.join(v)))
    L.append('matrix Y[4][5]; int i; int j; int k;')
    L.append('poly A; for(i=1;i<=4;i++){ A=kc*ph/4+ph*vv[i,1]+ETA*nn[i,1]; for(j=1;j<=5;j++){ Y[i,j]=A*m[j]; }')
    L.append(' Y[i,1]=Y[i,1]+(lam-1)*ETA*nn[i,1]+s2*(1-lam)*nn[i,1]+s3*(1-mu)*qv[i,1];')
    L.append(' Y[i,2]=Y[i,2]-(lam-1)*ETA*nn[i,1]+s2*(1+lam)*nn[i,1]+s3*(1+mu)*qv[i,1];')
    L.append(' Y[i,3]=Y[i,3]+s1*vv[i,1]; }')
    L.append('list C; matrix M[4][4]; int cc; poly F; matrix T;')
    L.append('for(j=1;j<=5;j++){ cc=0; for(k=1;k<=5;k++){ if(k!=j){ cc=cc+1; for(i=1;i<=4;i++){ M[i,cc]=1+Y[i,k]; } } } C[j]=p4(M)-24; }')
    L.append('ideal E; for(j=2;j<=5;j++){ F=C[j]-m[j]*C[1]; T=coef(F,s1*s2*s3*ph*et); for(k=1;k<=ncols(T);k++){ E=E,T[2,k]; } }')
    L.append('"NGEN",size(E);')
    L.append('ring R2=0,(%s),dp; ideal E=imap(R,E);'%','.join(unk))
    ex=[qn,qq,ip(v,['1']*4),ip(v,n),ip(v,q),'lam*mu-1','lam*(1-mb)-(1+mb)','kc^2-4/3*(%s)'%ip(v,v),'u*(%s)-1'%ip(n,q)]
    L.append('ideal I=E,%s; I=simplify(I,2+4+8);'%','.join(ex))
    tag='%s_%s_v%d%s'%(cn,cp,k,'_CAL' if cal else '')
    L.append('ideal G=std(I); if (size(G)==1 and G[1]==1) {"RES %s UNIT";} else {"RES %s NONUNIT dim",dim(G),"size",size(G);}'%(tag,tag))
    L.append('quit;')
    open('%s/x5i_%s.sing'%(out,tag),'w').write('\n'.join(L)+'\n')
print('written')
