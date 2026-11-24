# Round 24 (dlt0c): U' membership with EXPLICIT coefficients (D = al(a,b,e) u1 + be(a,b,e) u2, al/be with one unknown per monomial) instead of minors.
# Round 21: dim Delta = 0: H = {lam (x) h : sum lam = 0}, e_2(h) = e_3(h) = 0, s(h) = s (chart: s = 1 or s = 0 with h_K0 = 1); U' = span(u1, u2),
# u1 = h o h - s h, u2 = s h o h - h o h o h (chart: (0,1)-minor of (u1,u2) nonzero, WLOG by S_5). x* = (r_0, r_1, r_2) modulo H: gauge r_0[K] = r_1[K] = 0
# (K with h_K != 0: chart u4 h_K = 1); x*-chart r_{I,J} = 1. Cuts (rigorous, sec. 41 (F)): <r_i, s1 - h> equal, <r_i, h^2 - s h> = 0.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
SCH,K,XI,P=sys.argv[1],int(sys.argv[2]),sys.argv[3],sys.argv[4]
h=['h%d'%j for j in range(5)]; s='1' if SCH=='s1' else '0'
u1=['((%s)^2-(%s)*(%s))'%(h[j],s,h[j]) for j in range(5)]; u2=['((%s)*(%s)^2-(%s)^3)'%(s,h[j],h[j]) for j in range(5)]
r=[['r%d_%d'%(i,j) for j in range(5)] for i in range(3)]; r[0][K]='0'; r[1][K]='0'
I,J=int(XI[0]),int(XI[1]); r[I][J]='1'
co=['a','b','(-a-b)']
rows=[['(%s)*%s+e*%s'%(co[i],h[j],r[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
import itertools
EXTRA=[]
for _nm,_dg in (('c',1),('D2',2),('D3',3)):
    _n=len(list(itertools.combinations_with_replacement('abe',_dg))); EXTRA+=['A%s_%d'%(_nm,k) for k in range(_n)]+['B%s_%d'%(_nm,k) for k in range(_n)]
e2='+'.join('%s*%s'%(h[i],h[j]) for i,j in itertools.combinations(range(5),2)); e3='+'.join('%s*%s*%s'%(h[i],h[j],h[k]) for i,j,k in itertools.combinations(range(5),3))
ip=lambda x,y: '+'.join('(%s)*(%s)'%(x[j],y[j]) for j in range(5))
one_minus=['(%s-%s)'%(s,h[j]) for j in range(5)]
cuts=['(%s)-(%s)'%(ip(r[0],one_minus),ip(r[1],one_minus)),'(%s)-(%s)'%(ip(r[0],one_minus),ip(r[2],one_minus))]+[ip(r[i],u1) for i in range(3)]
vs=h+[x for row in r for x in row if x not in ('0','1')]+['u','u4']+EXTRA
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s,%s,%s-(%s),%s; int kk; int ll; matrix M; poly gg;'%(e2,e3,'+'.join(h),s,','.join(cuts)),
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
import itertools as _it
extra=[]
for nm,vec,dg in (('c',c,1),('D2',D2,2),('D3',D3,3)):
    mons=['*'.join(m) for m in _it.combinations_with_replacement(['a','b','e'],dg)]
    A=['A%s_%d'%(nm,k) for k in range(len(mons))]; B=['B%s_%d'%(nm,k) for k in range(len(mons))]; extra+=A+B
    alp='+'.join('%s*%s'%(A[k],mons[k]) for k in range(len(mons))); bet='+'.join('%s*%s'%(B[k],mons[k]) for k in range(len(mons)))
    for j in range(5):
        o.append('gg=(%s)-(%s)*(%s)-(%s)*(%s); M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(vec[j],alp,u1[j],bet,u2[j]))
o.append('C=C,u*((%s)*(%s)-(%s)*(%s))-1,u4*%s-1;'%(u1[0],u2[1],u1[1],u2[0],h[K]))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=%s(C); "DLT0B %s K=%d x*%s: dim",dim(std(G)),"unit",(G[1]==1);'%(P,','.join(vs),'slimgb' if P=='0' else 'std',SCH,K,XI))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r24/dlt0c_%s_%d_%s_%s.sing'%(SCH,K,XI,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
