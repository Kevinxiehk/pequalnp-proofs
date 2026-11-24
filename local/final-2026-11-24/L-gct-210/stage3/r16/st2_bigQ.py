# Round 17: RUNNABLE generator for COMPUTE-stage3 item 14(a): (PR3) stratum (II), sub-case dim Delta = 2, EXACT over Q (slimgb or std; never modStd).
#   X = H (+) C x*, H = {(a h_0, b h_1, (-a-b) h_2)}, Delta = c(H) = span(h_0 - h_2, h_1 - h_2) with basis f_0 = (1,0,p2,p3,-1-p2-p3),
#   f_1 = (0,1,q2,q3,-1-q2-q3) (WLOG by S_5: (0,1)-minor of Delta nonzero); h_2 = k, h_0 = k + l0 f_0 + m0 f_1, h_1 = k + l1 f_0 + m1 f_1,
#   u (l0 m1 - l1 m0) = 1.  x* = (r_0, r_1, -r_0 - r_1): WLOG zero column sums (c(x*) lies in U' = Delta = c(H); subtract an element of H).
#   Equations: all (a,b,d)-coefficients of sigma_1..3(x) and of the Delta-membership of c(x), D_2(x), D_3(x) (entries 2,3,4 of v - v_0 f_0 - v_1 f_1),
#   PLUS the hand-derived consequences (NOTES-stage3 sec. 37 (A)) as extra generators (they lie in the ideal; they only help the GB):
#     (S2m) <h_i, r_i> - s(h_i) s(r_i) equal for i = 0,1,2;   (S3m) <F_pq, r_t> = 0 with F_pq = 2 h_p o h_q - s(h_p + h_q);
#     (D2m) M_i - M_2 in Delta, M_i = s(r_i) h_i - 2 (h_i - (s/2) 1) o r_i  (s := s(h_2)).
#   Charts: sigma-chart 's1' (s(k) = 1) or 's0' (s(k) = 0 and l0 m1 - l1 m0 = 1); x*-chart: r_{i,j} = 1 (i in {0,1}, j in 0..4)  -> 20 charts.
#   Modes: 'full' (everything), 'lin' (only the d^0 and d^1 coefficients: x*-LINEAR relaxation -- unit => chart closed),
#          'cal'  (calibration: H-part only + 4 random integer linear slices; must be NON-unit (the H-part is a 4-dim family)).
# Usage: python3 -I st2_bigQ.py MODE SCHART I J [ALG] [P]   -> writes st2Q_<MODE>_<SCHART>_<I><J>.sing ; ALG = slimgb (default) | std ; P = 0 (default)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
mode,sch,I,J=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]); alg=sys.argv[5] if len(sys.argv)>5 else 'slimgb'; P=sys.argv[6] if len(sys.argv)>6 else '0'
I2,J2=(int(sys.argv[7]),int(sys.argv[8])) if mode=='twocol' else (None,None)
assert alg in ('slimgb','std')
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']; k=['k%d'%j for j in range(5)]
h2=k; h0=['(%s+l0*%s+m0*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]; h1=['(%s+l1*%s+m1*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]; H=[h0,h1,h2]
r0=['r0_%d'%j for j in range(5)]; r1=['r1_%d'%j for j in range(5)]
if mode=='colel':   # x* = w (x) e_J, w = (1, rho, -1-rho) (I = 0) or (0, 1, -1) (I = 1)
    r0=['0']*5; r1=['0']*5
    if I==0: r0[J]='1'; r1[J]='rho'
    else: r1[J]='1'
elif mode!='cal':
    if I==0: r0[J]='1'
    else: r1[J]='1'
r2=['(-(%s)-(%s))'%(r0[j],r1[j]) for j in range(5)]; R=[r0,r1,r2]
co=['a','b','(-a-b)']
dd='' if mode=='cal' else '+d*%s'
rows=[[('(%s)*%s'%(co[i],H[i][j]))+(('+d*%s'%R[i][j]) if mode!='cal' else '') for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
xv=([x for x in r0+r1 if x not in ('1','0','rho')]+(['rho'] if (mode=='colel' and I==0) else [])) if mode!='cal' else []
vs=['p2','p3','q2','q3']+k+['l0','m0','l1','m1']+xv+['u']+(['u3'] if (mode=='twocol' or (mode=='colel' and len(sys.argv)>9)) else [])
pv=['a','b']+(['d'] if mode!='cal' else [])
mono='*'.join(pv)
o=['ring R0=0,(%s,%s),dp;'%(','.join(vs),','.join(pv)),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int l; int t; matrix M; poly g;']
# level coefficients (in 'lin' mode keep only d-degree <= 1)
def keep(expr):
    return 'jet(%s,1,intvec(%s))'%(expr,','.join(['0']*len(vs)+['0','0','1'])) if mode=='lin' else expr
o.append('for(kk=1;kk<=ncols(L);kk++){ M=coef(%s,%s); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }'%(keep('L[kk]'),mono))
for j in range(5): o.append('poly F0_%d=%s; poly F1_%d=%s;'%(j,f0[j],j,f1[j]))
# Delta-membership of deletion vectors: residual vector w = v - v_0 f_0 - v_1 f_1 (entries 2,3,4), then all coefficients in (a,b,d)
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for m in (2,3,4):
        o.append('g=%s_%d-%s_0*F0_%d-%s_1*F1_%d; M=coef(%s,%s); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; }'%(nm,m,nm,m,nm,m,keep('g'),mono))
if mode!='cal':
    # hand-derived extra generators (S2m), (S3m), (D2m)
    ip=lambda x,y: '('+'+'.join('(%s)*(%s)'%(x[j],y[j]) for j in range(5))+')'
    sm=lambda x: '('+'+'.join(x)+')'
    s='(%s)'%sm(k)
    B=[ '(%s-%s*%s)'%(ip(H[i],R[i]),s,sm(R[i])) for i in range(3)]
    o.append('C=C,%s-%s,%s-%s;'%(B[0],B[2],B[1],B[2]))
    for (p,q,t) in ((0,1,2),(0,2,1),(1,2,0)):
        F=['(2*(%s)*(%s)-%s*((%s)+(%s)))'%(H[p][j],H[q][j],s,H[p][j],H[q][j]) for j in range(5)]
        o.append('C=C,%s;'%ip(F,R[t]))
    Mv=[['(%s*(%s)-2*((%s)-%s/2)*(%s))'%(sm(R[i]),H[i][j],H[i][j],s,R[i][j]) for j in range(5)] for i in range(3)]
    for i in (0,1):
        W=['(%s-(%s))'%(Mv[i][j],Mv[2][j]) for j in range(5)]
        for m in (2,3,4): o.append('C=C,%s-(%s)*F0_%d-(%s)*F1_%d;'%(W[m],W[0],m,W[1],m))
if sch=='s1': o.append('C=C,%s-1,u*(l0*m1-l1*m0)-1;'%'+'.join(k))
else: o.append('C=C,%s,l0*m1-l1*m0-1,u-1;'%'+'.join(k))
if mode=='twocol': o.append('C=C,u3*(%s)-1;'%(R[I2][J2]))
if mode=='colel' and len(sys.argv)>9:   # stratum (II) proper on the column-element locus: rho(1+rho) != 0 and h_i[c_i] != 0 (c_i != J)
    cs=[int(c) for c in sys.argv[7:10]]
    o.append('C=C,u3*rho*(1+rho)*(%s)*(%s)*(%s)-1;'%(H[0][cs[0]],H[1][cs[1]],H[2][cs[2]]))
if mode=='cal':
    import random; random.seed(17)
    hv=['p2','p3','q2','q3']+k+['l0','m0','l1','m1']
    for _ in range(4): o.append('C=C,%s;'%('+'.join('(%d)*%s'%(random.randint(-9,9),v) for v in hv)+'+(%d)'%random.randint(1,9)))
o.append('ring R=0,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%','.join(vs))
if P!='0': o[-1]=o[-1].replace('ring R=0,','ring R=%s,'%P)
o.append('"eqs",ncols(C); int t0=timer; ideal G=%s(C);'%alg)
o.append('"ST2Q %s %s %d%d %s"+"%s"+": dim",dim(std(G)),"unit",(G[1]==1),"time",timer-t0;'%(mode,sch,I,J,alg,(' second-col %d%d'%(I2,J2)) if mode=='twocol' else ''))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r16/st2Q_%s_%s_%d%d%s%s%s.sing'%(mode,sch,I,J,('_%d%d'%(I2,J2)) if mode=='twocol' else '',('_c'+''.join(sys.argv[7:10])) if (mode=='colel' and len(sys.argv)>9) else '','' if P=='0' else '_p')
open(f,'w').write('\n'.join(o)+'\n'); print(f)
