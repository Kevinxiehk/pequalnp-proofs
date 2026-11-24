# Round 16: (PR3) STRATUM (II), sub-case dim c(H) = 2.  H = {(a h_0, b h_1, c h_2) : a + b + c = 0} inside X (the three row kernels K_i are
# coplanar).  If dim c(H) = dim span(d_0, d_1) = 2 (d_i = h_i - h_2) and the defect of X is <= 2, then U' = span(d_0, d_1), so every deletion
# vector D_2(x), D_3(x) (x in H) lies in span(d_0, d_1).  System in h_0, h_1, h_2 only: level of H (all (a,b)-coefficients of sigma_1..3) and the
# membership minors det[d_0 d_1 v]_{rows 0,1,k} (k = 2,3,4) for every (a,b)-coefficient vector v of D_2, D_3; chart minor_{01}(d_0, d_1) != 0
# (WLOG by S_5).  Normalisation: 's1': s(h_2) = 1 and u minor = 1;  's0': s(h_2) = 0 and minor = 1 (scaling h -> lam h).
# Calibration modes: 'nodef' (level of H only: must be NON-unit), 'd2only' (defect conditions from D_2 only).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
mode,P=sys.argv[1],sys.argv[2]; cal=sys.argv[3] if len(sys.argv)>3 else ''
h=[['h%d_%d'%(i,j) for j in range(5)] for i in range(3)]
co=['a','b','(-a-b)']
rows=[['(%s)*%s'%(co[i],h[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
d=[['(%s-%s)'%(h[i][j],h[2][j]) for j in range(5)] for i in range(2)]
def dcoef(f,p,q):
    s=f
    for _ in range(p): s='diff(%s,a)'%s
    for _ in range(q): s='diff(%s,b)'%s
    return s
o=['ring R0=%s,(%s,u,a,b),dp;'%(P,','.join(h[0]+h[1]+h[2]))]
o.append('ideal L=%s;'%','.join(lev))
o.append('ideal C; int k; int l; matrix M;')
o.append('for(k=1;k<=ncols(L);k++){ M=coef(L[k],a*b); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }')
for j in range(5): o.append('poly d0_%d=%s; poly d1_%d=%s;'%(j,d[0][j],j,d[1][j]))
blocks=[] if cal=='nodef' else ([(D2,2)] if cal=='d2only' else [(D2,2),(D3,3)])
nv=0
for vec,deg in blocks:
    for j in range(5): o.append('poly E%d=%s;'%(j,vec[j]))
    for p in range(deg+1):
        for j in range(5): o.append('poly v%d_%d=%s;'%(nv,j,dcoef('E%d'%j,p,deg-p)))
        for k in (2,3,4):
            o.append('C=C,det(matrix(ideal(d0_0,d1_0,v%d_0, d0_1,d1_1,v%d_1, d0_%d,d1_%d,v%d_%d),3,3));'%(nv,nv,k,k,nv,k))
        nv+=1
mn='(d0_0*d1_1-d0_1*d1_0)'
if mode=='s1': o.append('C=C,%s-1,u*%s-1;'%('+'.join(h[2]),mn))
else: o.append('C=C,%s,%s-1;'%('+'.join(h[2]),mn))
o.append('ring R=%s,(%s,u),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(h[0]+h[1]+h[2])))
o.append('"eqs",ncols(C); int t0=timer; ideal G=std(C);')
o.append('"strat2 %s %s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;'%(mode,cal))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r16/st2_%s%s_%s.sing'%(mode,cal,'p' if P!='0' else 'q')
open(f,'w').write('\n'.join(o)+'\n'); print(f)
