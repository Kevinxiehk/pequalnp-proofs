# Round 23: the WHOLE k_N = 2 special family, t a ring variable: rows 0,1 m = (1,w^2,w,0,0); row 2 n2 = (t,t,t,1,-3t-1); row 3 n3 = (3t+2,3t+2,3t+2,-12t-3,3t-3)
# (n2 . n3 = 0 identically; t = 0 is the round-22 member). Pair test for (r,k): third element xi on rows {l,n,4}, gauges xi_2[3] = 0, xi_3[0] = 0 (row 3 needs
# 3t+2 != 0: hinge u0*(3t+2) = 1 added), chart XC = 1. Optional HV = variable whose vanishing is tested (hinge u1*HV = 1: unit <=> HV = 0 on all solutions).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
r,k,XC=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; HV=sys.argv[4] if len(sys.argv)>4 else ''
W={0:['1','w^2','w','0','0'],1:['1','w^2','w','0','0'],2:['t','t','t','1','(-3*t-1)'],3:['(3*t+2)','(3*t+2)','(3*t+2)','(-12*t-3)','(3*t-3)']}
gauge={0:0,1:0,2:3,3:0}
l,n=[i for i in range(4) if i not in (r,k)]
xl=['xl%d'%j for j in range(5)]; xn=['xn%d'%j for j in range(5)]; v=['v%d'%j for j in range(5)]
xl[gauge[l]]='0'; xn[gauge[n]]='0'
for L in (xl,xn,v):
    if XC in L: L[L.index(XC)]='1'
rows=[]
for i in range(5):
    if i in (r,k): rows.append(['c%d*(%s)'%(i,W[i][j]) for j in range(5)])
    elif i==l: rows.append(['al*(%s)+c%d*(%s)'%(xl[j],i,W[i][j]) for j in range(5)])
    elif i==n: rows.append(['al*(%s)+c%d*(%s)'%(xn[j],i,W[i][j]) for j in range(5)])
    else: rows.append(['al*(%s)'%v[j] for j in range(5)])
lev=[sig(rows,s,range(5)) for s in range(1,6)]
vs=[x for x in xl+xn+v if x not in ('0','1')]
o=['ring R0=(0,w),(%s,t,u0,u1,al,c0,c1,c2,c3),dp; minpoly=w^2+w+1;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }',
   'C=C,u0*(3*t+2)-1;'+('C=C,u1*(%s)-1;'%HV if HV else ''),
   'ring R=(0,w),(%s,t,u0,u1),dp; minpoly=w^2+w+1; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%','.join(vs),
   '"kn2fam pair (%d,%d) xi=%s HV=%s: dim",dim(G),"unit",(G[1]==1); if(G[1]!=1 && size(G)<40){print(G);}'%(r,k,XC,HV),'quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r22/kn2fam_%d%d_%s_%s.sing'%(r,k,XC,HV or 'no'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
