# Round 18: (PR3) STRATUM (III), sub-case dim c(Y) = 2. X = Y (+) C x*, Y = K_0 = {(0, v, Av)} (2-dim, rows 1,2), row 0 of X = C p.
# Delta := c(Y) (2-dim, WLOG (S_5) (0,1)-minor nonzero): basis f_0 = (1,0,p2,p3,*), f_1 = (0,1,q2,q3,*), Y = span(y_k = (0, v_k, f_k - v_k)), k = 0,1.
# Defect <= 2 => U' = Delta => WLOG x* has zero column sums; rows in planes => r_1 in P_1 = span(v_0, v_1), r_2 in P_2 = span(f_0-v_0, f_1-v_1):
#   r_1 = l0 v_0 + l1 v_1,  r_2 = m0 (f_0-v_0) + m1 (f_1-v_1),  p = -r_1 - r_2.
# Equations: all (a,b,t)-coefficients of sigma_1..3 and Delta-membership of c, D_2, D_3 for x = a y_0 + b y_1 + t x*.
# MODE 'pp I J': Rabinowitsch u p_I p_J = 1 (p has >= 2 nonzero entries)   -> UNIT expected if p must be a unit vector.
#      'col I J': p = e-vector assumed? (later)   'cal': only u (l0 - m0, l1 - m1)-hinge chart ... (calibration: family must survive)
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
mode=sys.argv[1]; P=sys.argv[2]; args=sys.argv[3:]
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']
v0=['v0_%d'%j for j in range(5)]; v1=['v1_%d'%j for j in range(5)]
u0=['(%s-%s)'%(f0[j],v0[j]) for j in range(5)]; u1=['(%s-%s)'%(f1[j],v1[j]) for j in range(5)]
r1=['(l0*%s+l1*%s)'%(v0[j],v1[j]) for j in range(5)]; r2=['(m0*%s+m1*%s)'%(u0[j],u1[j]) for j in range(5)]
p=['(-%s-%s)'%(r1[j],r2[j]) for j in range(5)]
rows=[['t*%s'%p[j] for j in range(5)],['a*%s+b*%s+t*%s'%(v0[j],v1[j],r1[j]) for j in range(5)],['a*%s+b*%s+t*%s'%(u0[j],u1[j],r2[j]) for j in range(5)]]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['p2','p3','q2','q3']+v0+v1+['l0','l1','m0','m1','u']
o=['ring R0=0,(%s,a,b,t),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int l; matrix M; poly g;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*t); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }']
for j in range(5): o.append('poly F0_%d=%s; poly F1_%d=%s;'%(j,f0[j],j,f1[j]))
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for m in (2,3,4): o.append('g=%s_%d-%s_0*F0_%d-%s_1*F1_%d; M=coef(g,a*b*t); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; }'%(nm,m,nm,m,nm,m))
if mode=='pp':
    I,J=int(args[0]),int(args[1]); o.append('C=C,u*(%s)*(%s)-1;'%(p[I],p[J]))
o.append('ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(vs)))
o.append('"eqs",ncols(C); int t0=timer; ideal G=std(C); "ST3 %s %s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;'%(mode,' '.join(args)))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r18/st3_%s_%s_%s.sing'%(mode,''.join(args),'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
