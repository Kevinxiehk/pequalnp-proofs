# Round 20: dim Delta = 0: h_0 = h_1 = h_2 = h, H = {lam (x) h : sum lam = 0}; level of H <=> e_2(h) = e_3(h) = 0; D_2(H) = C (h o h - s h), D_3(H) = C (s h^2 - h^3).
# X = H (+) C x*. Defect <= 2: U' (2-dim) contains c(X), D_2(X), D_3(X). Chart: U' = span(f0, f1) (Delta-chart as before: f0 = (1,0,p2,p3,*), f1 = (0,1,q2,q3,*)).
# x*-chart r_{I,J} = 1 (x* mod H: we may subtract lam (x) h; normalise r_2 freely? -- keep x* general with chart). Global scale: h -> la h: chart h_K = 1.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
K,XI,P=int(sys.argv[1]),sys.argv[2],sys.argv[3]
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']
h=['h%d'%j for j in range(5)]; h[K]='1'
r=[['r%d_%d'%(i,j) for j in range(5)] for i in range(3)]
I,J=int(XI[0]),int(XI[1]); r[I][J]='1'
# gauge: x* mod H = {lam (x) h, sum lam = 0}: normalise r_0[K] = r_1[K] = 0 if (I,J) allows (subtract lam_0 h, lam_1 h, lam_2 = -lam_0 - lam_1)
if not (J==K and I in (0,1)):
    r[0][K]='0'; r[1][K]='0'
co=['a','b','(-a-b)']
rows=[['(%s)*%s+e*%s'%(co[i],h[j],r[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['p2','p3','q2','q3']+[x for x in h if x!='1']+[x for row in r for x in row if x not in ('0','1')]
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M; poly gg;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
for j in range(5): o.append('poly F0_%d=%s; poly F1_%d=%s;'%(j,f0[j],j,f1[j]))
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for m in (2,3,4): o.append('gg=%s_%d-%s_0*F0_%d-%s_1*F1_%d; M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(nm,m,nm,m,nm,m))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C); "DLT0 hchart %d x*chart %s: dim",dim(G),"unit",(G[1]==1);'%(P,','.join(vs),K,XI))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r20/dlt0_%d_%s_%s.sing'%(K,XI,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
