# Round 24 (eqtA_cls): CLASS-REDUCED version. The hand cut G in U' makes w a root of one fixed quadric on S, so (non-degenerate case) w takes exactly
# two values on S (two values needed for dim U' = 2); the cut F_ww in U' then fixes d_j as a function of w_j. CLS (argv[7]) = class string on S
# (CLS[0] = '0', CLS[1] = '1'); d stays general (no d-class assumption); CLS = 'deg': the quadric vanishes identically (be = 2, ga = 0, 3 al + 4 s + ep = 0), w general.
# Round 22: EQUAL t's, case A (U' = span(d, w o d)), s = 1. Columns: S = {0..nS-1} (supp d), F (w = h = 1, free 3-row columns of H), Z0 (w = h = 0).
# H = {(a w, b w, c h) : a+b+c = 0}, h = w - d; level of H and all of X, deletion vectors in U' (membership via 3x3 minors of [d, w o d, v] on rows
# {0,1,k}; chart u2 * minor_{01}(d, w o d) = 1, WLOG by S_nS on S if nS >= 2). x*: c(x*) = ka (w o d) after subtracting H (c(H) = C d); ka = 0 with chart
# r_{I,J} = 1 or ka = 1. Also u3: d has full support on S (d_j != 0 for j in S).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
nS,nF,KA,XI,P=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),sys.argv[4],sys.argv[5]
nZ=5-nS-nF; assert nS>=2 and nZ>=0
HG=sys.argv[6] if len(sys.argv)>6 else ''
if HG=='-': HG=''
CLS=sys.argv[7]
if CLS=='deg':
    w=['w%d'%j for j in range(nS)]+['1']*nF+['0']*nZ
    d=['d%d'%j for j in range(nS)]+['0']*(nF+nZ)
else:
    assert len(CLS)==nS and CLS[0]=='0' and CLS[1]=='1'
    w=[('wA','wB')[int(c)] for c in CLS]+['1']*nF+['0']*nZ
    d=['d%d'%j for j in range(nS)]+['0']*(nF+nZ)   # d kept general: the F_ww cut fixes d_j only where al + be w_j != 0
h=['(%s-%s)'%(w[j],d[j]) for j in range(5)]
wd=['(%s*%s)'%(w[j],d[j]) for j in range(5)]
r0=['r0_%d'%j for j in range(5)]; r1=['r1_%d'%j for j in range(5)]
if KA==0: I,J=int(XI[0]),int(XI[1]); (r0 if I==0 else r1)[J]='1'
r2=['(-(%s)-(%s)%s)'%(r0[j],r1[j],('-'+wd[j]) if KA==1 else '') for j in range(5)]
H=[w,w,h]; R=[r0,r1,r2]; co=['a','b','(-a-b)']
rows=[['(%s)*%s+e*%s'%(co[i],H[i][j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=list(dict.fromkeys([x for x in w+d if x not in ('0','1')]))+[x for x in r0+r1 if x not in ('0','1')]+['u2','u3','al','be','ga','ep']+(['uh'] if HG else [])
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M; poly gg;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for k in range(2,5):
        o.append('gg=det(matrix(ideal(%s,%s,%s_0, %s,%s,%s_1, %s,%s,%s_%d),3,3)); M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(d[0],wd[0],nm,d[1],wd[1],nm,d[k],wd[k],nm,k))
o.append('C=C,u2*((%s)*(%s)-(%s)*(%s))-1,u3*%s-1;'%(d[0],wd[1],d[1],wd[0],'*'.join(d[:nS])))
sg='('+'+'.join(w)+')'
# hand cuts (case A, sec. 41 (E)/42): F_ww in U' = span(d, w o d): off S automatic; on S 2 w_j (w_j - s) = d_j (al + be w_j); G in U': on S
# (6 - 3 be) w_j^2 - (3 al + 4 s) w_j = ga + ep w_j  (s = s(w))
cuts=['2*%s*(%s-%s)-%s*(al+be*%s)'%(w[j],w[j],sg,d[j],w[j]) for j in range(nS)]+['(6-3*be)*(%s)^2-(3*al+4*%s)*%s-ga-ep*%s'%(w[j],sg,w[j],w[j]) for j in range(nS)]
o.append('C=C,%s;'%','.join(cuts))
if CLS=='deg': o.append('C=C,be-2,ga,3*al+4*%s+ep;'%sg)
if '+' in HG:
    hj,rg_=HG.split('+'); i,a,b=int(rg_[0]),int(rg_[1]),int(rg_[2])
    o.append('C=C,uh*(%s)*((%s)*(%s)-(%s)*(%s))-1;'%(h[int(hj[1])],H[i][a],R[i][b],H[i][b],R[i][a]))
elif HG.startswith('h'):   # h != 0 hinge: uh * h_j = 1
    o.append('C=C,uh*(%s)-1;'%h[int(HG[1])])
elif HG:   # stratum hinge on row i: minor (a,b) of (h_i, r_i) nonzero
    i,a,b=int(HG[0]),int(HG[1]),int(HG[2])
    o.append('C=C,uh*((%s)*(%s)-(%s)*(%s))-1;'%(H[i][a],R[i][b],H[i][b],R[i][a]))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=%s(C); "EQTA nS=%d nF=%d ka=%d x*%s: dim",dim(std(G)),"unit",(G[1]==1);'%(P,','.join(vs),'slimgb' if P=='0' else 'std',nS,nF,KA,XI))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r24/eqtAc_%d%d_%d_%s%s_%s_%s.sing'%(nS,nF,KA,XI,('_h'+HG) if HG else '',CLS,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
