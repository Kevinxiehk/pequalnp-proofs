# verify2 r24: my own generator for (SM_n) in rank 2 (nondegenerate plane U = span(f,f')), ORIGINAL Walsh coordinates over Q(i)
# (no REAL trick): c(s) = (s^2-1, I(s^2+1), 2s) isotropic; columns y_k = a_k f (S0) or f/2 + b_k f' (S1); sum y = f.
# Conditions: sigma_k(Y minus column j) = 0 for k = 2,3,4 and every j (all deletions; columns lie in 1-perp of C^4 so sigma_1 = 0).
# Open conditions: rz*(sg-sp)*prod a*prod b = 1.  usage: python3 -I r2c_mine.py NC S1SIZE CHAR OUT
import sys, itertools
NC,s1,P,out=int(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4]
S1=list(range(1,s1+1)); S0=list(range(s1+1,NC+1))
unk=['sg','sp']+['a%d'%k for k in S0]+['b%d'%k for k in S1]+['rz']
L=['ring R=(%s,I),(t,%s),dp; minpoly=I^2+1; option(redSB);'%(P,','.join(unk))]
H=[[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]]
def c(s): return ['(%s^2-1)'%s,'I*(%s^2+1)'%s,'(2*%s)'%s]
f=c('sg'); fp=c('sp')
cols={}
for k in range(1,NC+1):
    if k in S0: v=['a%d*%s'%(k,x) for x in f]
    else: v=['(%s/2+b%d*%s)'%(x,k,y) for x,y in zip(f,fp)]
    cols[k]=['(%s)'%'+'.join('(%d)*%s'%(H[r][q],v[q]) for q in range(3)) for r in range(4)]
for k in cols:
    for r in range(4): L.append('poly y%d_%d=%s;'%(r,k,cols[k][r]))
lin=[]
if S1: lin.append('+'.join('b%d'%k for k in S1))
lin.append('(%s)-(1-%d/2)'%('+'.join('a%d'%k for k in S0) if S0 else '0',s1))
L.append('ideal E=%s, rz*(sg-sp)*%s-1;'%(','.join(lin),'*'.join(['a%d'%k for k in S0]+['b%d'%k for k in S1]+['1'])))
# permanent of J + t*Y^(j): explicit expansion over the 24 bijections rows -> remaining columns
L.append('ideal C;')
for j in range(1,NC+1):
    rest=[k for k in range(1,NC+1) if k!=j][:4] if NC==5 else [k for k in range(1,NC+1)]
    if NC==5: rest=[k for k in range(1,6) if k!=j]
    terms=[]
    for p in itertools.permutations(range(4)):
        terms.append('*'.join('(1+t*y%d_%d)'%(r,rest[p[r]]) for r in range(4)))
    L.append('poly F%d=%s-24;'%(j,'+'.join(terms)))
    L.append('matrix T%d=coeffs(F%d,t); int kk; for(kk=3;kk<=nrows(T%d);kk++){ C=C,T%d[kk,1]; }'%(j,j,j,j))
    L.append('if(subst(F%d,t,0)!=0){ "ERROR const"; } if(nrows(T%d)>=2){ if(T%d[2,1]!=0){ "ERROR deg1 nonzero"; } }'%(j,j,j))
    if NC==4: break
L.append('ring R2=(%s,I),(%s),dp; minpoly=I^2+1; option(redSB); ideal G=imap(R,C),imap(R,E); ideal I0=std(G);'%(P,','.join(unk)))
L.append('printf("MINE RANK2 n=%d |S1|=%d char %s over Q(i): dim %%s unit %%s",dim(I0),(reduce(1,I0)==0));'%(NC,s1,P))
L.append('quit;')
open(out,'w').write('\n'.join(L)+'\n'); print('written',out)
