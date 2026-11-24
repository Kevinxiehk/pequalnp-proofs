# Round 23: block family B (contains the (2,1,1) member B and, at t^2+t+1 = 0, the (2,2) member): rows 0,1: m' = (a,a,a,1,b), 6a^2+3a+1 = 0, b = -1-3a
# (isotropic, zero sum, constant on the block {0,1,2}); rows 2,3: n2 = (1,t,-1-t,0,0), n3 = (1+2t,-(2+t),1-t,0,0) (orthogonal basis of V_Z; <n2,n3> = 0
# identically). Pair test for (r,k) as in kn2_fam.py; a is a ring variable with its relation (dim/vdim count conjugates). Gauges: rows 0,1 col 3
# (m'_3 = 1), row 2 col 0 (n2_0 = 1), row 3 col 0 (needs 1+2t != 0: hinge u0 (1+2t) = 1). HV: hinge u1*HV = 1 (or 'T=<val>' fixes t).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import sig
r,k,XC=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]; HV=sys.argv[4] if len(sys.argv)>4 else ''
mp=['a','a','a','1','(-1-3*a)']
W={0:mp,1:mp,2:['1','t','(-1-t)','0','0'],3:['(1+2*t)','(-2-t)','(1-t)','0','0']}
gauge={0:3,1:3,2:0,3:0}
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
extra='C=C,u0*(1+2*t)-1;'
if HV.startswith('T='): extra+='C=C,t-(%s),u1;'%HV[2:]
elif HV: extra+='C=C,u1*(%s)-1;'%HV
else: extra+='C=C,u1;'
pr='*'.join(vs+['u0','u1'])
o=['ring R0=(0,a),(%s,t,u0,u1,al,c0,c1,c2,c3),dp; minpoly=6*a^2+3*a+1;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C; int kk; int ll; matrix M;',
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],al*c0*c1*c2*c3); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }', extra,
   'ring R=(0,a),(%s,t,u0,u1),dp; minpoly=6*a^2+3*a+1; ideal C=imap(R0,C); C=simplify(C,2); ideal G=std(C);'%','.join(vs),
   '"famB pair (%d,%d) xi=%s HV=%s: dim",dim(G),"vdim",vdim(G),"unit",(G[1]==1);'%(r,k,XC,HV),
   'if(G[1]!=1 && dim(G)>0){ ideal E=eliminate(G,%s); "t-proj:",E; }'%pr,
   'if(G[1]!=1 && dim(G)==0){ LIB "solve.lib"; def SOL=solve(G,8,0,"nodisplay"); setring SOL; int ii; int jj; for(ii=1;ii<=size(SOL);ii++){ string ss="PT"; for(jj=1;jj<=size(SOL[ii]);jj++){ ss=ss+" "+string(SOL[ii][jj]); } ss; kill ss; } }','quit;']
f='/home/kevxhk/work/L-gct-210/stage3/r22/famB_%d%d_%s_%s.sing'%(r,k,XC,(HV or 'no').replace('=','').replace('/','_').replace('*','')); open(f,'w').write('\n'.join(o)+'\n'); print(f)
