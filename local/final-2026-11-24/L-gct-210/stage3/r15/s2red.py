# Round 15: (alpha1) |supp W| = 2, W = v (e_0 - e_1)^T. After LEMMA S2 + S-SPEC the 3-dim subspace K_f = {Y(s) + mu Z : s in f^perp} is one of
#  (c3): n_2 = n_3 = n, gamma_2 = gamma_3 = gam on f^perp, v SPECIAL (= chi_1 WLOG):
#        y_0 = s/2 + m v, y_1 = s/2 + (sig(s) - m) v, y_2 = y_3 = s/2 + gam(s) n, y_4 = -s - sig(s) v - 2 gam(s) n
#  (c1): n_2 = v, gamma_2 = sig, n_3 SPECIAL (= chi_1 WLOG):
#        y_0 = s/2 + m v, y_1 = s/2 + (sig(s) - m) v, y_2 = s/2 + sig(s) v, y_3 = s/2 + gam(s) n_3, y_4 = -s - 2 sig(s) v - gam(s) n_3
#  with sig, gam NOT proportional (u (sig1 gam2 - sig2 gam1) = 1). f^perp = span(p, q) in the 3 Gr(2,3) charts; the free isotropic direction
#  (n in (c3), v in (c1)) = w(tau) or chi_3. Line conditions of every element of K_f (params s1, s2, m), chi-coordinates over Q.
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r15'); from chilib import line_eqs
case,chart,iso,P=sys.argv[1],int(sys.argv[2]),sys.argv[3],sys.argv[4]; CAL=sys.argv[5] if len(sys.argv)>5 else ''
i,j,k=[(0,1,2),(0,2,1),(1,2,0)][chart]
p=['0','0','0']; q=['0','0','0']; p[i]='1'; p[k]='x'; q[j]='1'; q[k]='y'
s=['(s1*(%s)+s2*(%s))'%(p[r],q[r]) for r in range(3)]
free=['1','2*tau','-2*tau^2'] if iso=='w' else ['0','0','1']
spec=['1','0','0']
sig='(sig1*s1+sig2*s2)'; gam='(gam1*s1+gam2*s2)'
add=lambda *v: ['('+'+'.join(x[r] for x in v)+')' for r in range(3)]
sc=lambda c,v: ['(%s)*(%s)'%(c,x) for x in v]
h=sc('1/2',s)
if CAL in ('line','line0'):   # restrict to the S2= line s in ker sig, m = 0 (calibration: must be NON-unit)
    s=['((sig2*(%s)-sig1*(%s))*s1)'%(p[r],q[r]) for r in range(3)]; h=sc('1/2',s); sig='0'
if case=='c3':
    v,n=spec,free
    Y=[add(h,sc('m',v)),add(h,sc('(%s-m)'%sig,v)),add(h,sc(gam,n)),add(h,sc(gam,n)),add(sc(-1,s),sc('-'+sig,v),sc('-2*'+gam,n))]
else:
    v,n3=free,spec
    Y=[add(h,sc('m',v)),add(h,sc('(%s-m)'%sig,v)),add(h,sc(sig,v)),add(h,sc(gam,n3)),add(sc(-1,s),sc('-2*'+sig,v),sc('-'+gam,n3))]
if CAL=='line0': Y=[[e.replace('m','0') if False else e for e in col] for col in Y]
eqs=line_eqs(Y)
if CAL=='d2': eqs=eqs[:4]
if CAL=='d3': eqs=eqs[:8]
vs='x,y,sig1,sig2,gam1,gam2'+(',tau' if iso=='w' else '')+',u'
out='/home/kevxhk/work/L-gct-210/stage3/r15/red_%s_%d%s_%s%s.sing'%(case,chart,iso,'p' if P!='0' else 'q',CAL)
with open(out,'w') as fh:
    fh.write('ring R0=%s,(%s,s1,s2,m),dp;\nideal E=\n%s;\n'%(P,vs,',\n'.join(eqs)))
    if CAL=='line0': fh.write('E=subst(E,m,0);\n')
    fh.write('ideal C; int a; int b; matrix M;\nfor(a=1;a<=ncols(E);a++){ M=coef(E[a],s1*s2*m); for(b=1;b<=ncols(M);b++){ C=C+ideal(M[2,b]); } }\n')
    fh.write('ring R=%s,(%s),dp;\noption(redSB);\nideal C=imap(R0,C);\nC=C,u*(sig1*gam2-sig2*gam1)-1;\nint t0=timer;\nideal G=std(C);\n'%(P,vs))
    fh.write('"%s chart %d %s: dim",dim(G),"unit",(G[1]==1),"time",timer-t0;\nquit;\n'%(case,chart,iso))
print(out)
