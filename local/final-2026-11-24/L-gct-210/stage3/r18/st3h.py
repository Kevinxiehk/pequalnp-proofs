# Round 18: STRATUM (III) via the H-plane. In stratum (III) the kernel elements x' = (w, s, 0) in K_2 and x'' = (w, 0, g) in K_1 span an H-plane
# {(A h_0, B h_1, C h_2) : A + B + C = 0} (h_0 = w), so X = H (+) C x*, i.e. stratum (III) = the part r_0 || h_0 of the hinge-free stratum-(II)
# system. Sub-case dim c(H) = 2: Delta-chart as in r16/st2_bigQ.py, x* = (lam h_0, r_1, -lam h_0 - r_1) (zero column sums).
# MODE 'pp I J' : u * h_0[I] * h_0[J] = 1 (h_0 has two nonzero entries) -> UNIT  <=>  h_0 is a unit vector on every solution.
# MODE 'any'    : no extra condition (calibration: must be NON-unit -- the family (E) lives here).
# Charts: SCH = 's1' (s(h_2) = 1, u2 (l0 m1 - l1 m0) = 1) or 's0'; XCH = 'L' (lam = 1) or 'Rj' (lam = 0, r_1[j] = 1).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
mode,sch,xch,P=sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4]; args=sys.argv[5:]
f0=['1','0','p2','p3','(-1-p2-p3)']; f1=['0','1','q2','q3','(-1-q2-q3)']; k=['k%d'%j for j in range(5)]
h2=k; h0=['(%s+l0*%s+m0*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]; h1=['(%s+l1*%s+m1*%s)'%(k[j],f0[j],f1[j]) for j in range(5)]; H=[h0,h1,h2]
r1=['r1_%d'%j for j in range(5)]
if xch=='L': lam='1'
else: lam='0'; r1[int(xch[1:])]='1'
r0=['(%s)*%s'%(lam,h0[j]) for j in range(5)]; r2=['(-(%s)-(%s))'%(r0[j],r1[j]) for j in range(5)]; R=[r0,r1,r2]
co=['a','b','(-a-b)']
rows=[['(%s)*%s+d*%s'%(co[i],H[i][j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); c,D2,D3=deletion(rows)
vs=['p2','p3','q2','q3']+k+['l0','m0','l1','m1']+[x for x in r1 if x!='1']+['u','u2']
o=['ring R0=0,(%s,a,b,d),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int l; matrix M; poly g;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*d); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; } }']
for j in range(5): o.append('poly F0_%d=%s; poly F1_%d=%s;'%(j,f0[j],j,f1[j]))
for nm,vec in (('c',c),('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for m in (2,3,4): o.append('g=%s_%d-%s_0*F0_%d-%s_1*F1_%d; M=coef(g,a*b*d); for(l=1;l<=ncols(M);l++){ C=C,M[2,l]; }'%(nm,m,nm,m,nm,m))
o.append(('C=C,%s-1,u2*(l0*m1-l1*m0)-1;'%'+'.join(k)) if sch=='s1' else ('C=C,%s,l0*m1-l1*m0-1,u2-1;'%'+'.join(k)))
if mode=='pp': o.append('C=C,u*(%s)*(%s)-1;'%(h0[int(args[0])],h0[int(args[1])]))
else: o.append('C=C,u-1;')
o.append('ring R=%s,(%s),dp; option(redSB); ideal C=imap(R0,C); C=simplify(C,2);'%(P,','.join(vs)))
o.append('"eqs",ncols(C); int t0=timer; ideal G=std(C); "ST3H %s %s %s %s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;'%(mode,sch,xch,' '.join(args)))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r18/st3h_%s%s_%s_%s_%s.sing'%(mode,''.join(args),sch,xch,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
