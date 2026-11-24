# Round 16: (PR3) STRATUM (II), sub-case dim c(H) = 2, in ADAPTED coordinates.  Delta := c(H) = span(h_0 - h_2, h_1 - h_2) (2-dim, inside 1^perp);
# WLOG (S_5) its (0,1)-minor is nonzero, so Delta has the basis f_0 = (1,0,p2,p3,-1-p2-p3), f_1 = (0,1,q2,q3,-1-q2-q3).  Rows:
#   h_2 = k,  h_0 = k + l0 f_0 + m0 f_1,  h_1 = k + l1 f_0 + m1 f_1,   u (l0 m1 - l1 m0) = 1  (Delta = span(d_0, d_1) exactly).
# Defect <= 2 forces U' = Delta, so every (a,b)-coefficient vector v of D_2(x), D_3(x) (x = (a h_0, b h_1, (-a-b) h_2)) lies in Delta:
#   v - v_0 f_0 - v_1 f_1 = 0 (entries 2,3,4).  Plus level of H (all coefficients of sigma_1..3).  Normalisation: 's1': s(k) = 1 (scaling);
#   's0': s(k) = 0 and l0 m1 - l1 m0 = 1.   Calibration 'nodef': level only (NON-unit expected); 'd2only'.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
mode,P=sys.argv[1],sys.argv[2]; cal=sys.argv[3] if len(sys.argv)>3 else ''
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']; k=['k%d'%j for j in range(5)]
h2=k; h0=['(%s+l0*%s+m0*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]; h1=['(%s+l1*%s+m1*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]
co=['a','b','(-a-b)']; H=[h0,h1,h2]
rows=[['(%s)*%s'%(co[i],H[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
def dcoef(f,p,q):
    s=f
    for _ in range(p): s='diff(%s,a)'%s
    for _ in range(q): s='diff(%s,b)'%s
    return s
vs='p2,p3,q2,q3,k0,k1,k2,k3,k4,l0,m0,l1,m1,u'
o=['ring R0=%s,(%s,a,b),dp;'%(P,vs)]
o.append('ideal L=%s;'%','.join(lev))
o.append('ideal C; int kk; int l; matrix M;')
o.append('for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }')
for j in range(5): o.append('poly F0_%d=%s; poly F1_%d=%s;'%(j,f0[j],j,f1[j]))
blocks=[] if cal=='nodef' else ([(D2,2)] if cal=='d2only' else [(D2,2),(D3,3)])
nv=0
for vec,deg in blocks:
    for j in range(5): o.append('poly E%d=%s;'%(j,vec[j]))
    for p in range(deg+1):
        for j in range(5): o.append('poly v%d_%d=%s;'%(nv,j,dcoef('E%d'%j,p,deg-p)))
        for m in (2,3,4): o.append('C=C,v%d_%d-v%d_0*F0_%d-v%d_1*F1_%d;'%(nv,m,nv,m,nv,m))
        nv+=1
if mode=='s1': o.append('C=C,k0+k1+k2+k3+k4-1,u*(l0*m1-l1*m0)-1;')
else: o.append('C=C,k0+k1+k2+k3+k4,l0*m1-l1*m0-1,u-1;')
o.append('ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,vs))
o.append('"eqs",ncols(C); int t0=timer; ideal G=std(C);')
o.append('"strat2b %s %s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;'%(mode,cal))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r16/st2b_%s%s_%s.sing'%(mode,cal,'p' if P!='0' else 'q')
open(f,'w').write('\n'.join(o)+'\n'); print(f)
