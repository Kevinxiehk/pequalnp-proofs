# Round 14: SHAPE S2 in conic coordinates: Y = a (x) (1,1,1,1,-2) + b2 (x) (e_2 - e_4) + b3 (x) (e_3 - e_4), b_k = be_k w(tau_k) (finite charts),
# a in V with chart a_i = 1. Singular-native over Q(i): dimension of the line-condition variety, and whether b's are forced special (p_3 = 0).
import itertools, subprocess, sys
i=int(sys.argv[1]) if len(sys.argv)>1 else 0
chi=[['1','1','1','1'],['1','I','-1','-I'],['1','-1','1','-1'],['1','-I','-1','I']]
def wv(tau,be): return ['(%s)*((%s)+2*(%s)*(%s)-2*(%s)^2*(%s))'%(be,chi[1][r],tau,chi[2][r],tau,chi[3][r]) for r in range(4)]
av=['a0','a1','a2']; a=list(av)+['(-(a0+a1+a2))']; a[i]='1'; a[3]='(-(%s+%s+%s))'%(a[0],a[1],a[2])
vs=[x for k,x in enumerate(av) if k!=i]+['be2','t2','be3','t3']
b2=wv('t2','be2'); b3=wv('t3','be3')
out=['ring R=(0,I),(%s,t),dp;'%','.join(vs+['u']),'minpoly=I^2+1;','matrix Y[4][5];']
for r in range(4):
    out.append('Y[%d,1]=%s; Y[%d,2]=%s; Y[%d,3]=%s+%s; Y[%d,4]=%s+%s; Y[%d,5]=-2*%s-%s-%s;'%(r+1,a[r],r+1,a[r],r+1,a[r],b2[r],r+1,a[r],b3[r],r+1,a[r],b2[r],b3[r]))
perms=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[pp[r]]+1) for r in range(4)) for pp in perms)+';')
out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
out.append('for(k=1;k<=4;k++){ M=coef(D[k],t); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} } J=simplify(J,2);')
out.append('ideal J0=J,u*be2*be3-1; ideal G=std(J0); "S2c chart %d (b2,b3 != 0): dim",dim(G);'%i)
p3='+'.join('(%s)^3'%x for x in b2); q3='+'.join('(%s)^3'%x for x in b3)
out.append('ideal G2=std(J,1-u*be2*be3*(%s)*(%s)); "S2c chart %d with p3(b2) p3(b3) != 0: dim",dim(G2);'%(p3,q3,i))
out.append('quit;')
fn='/home/kevxhk/work/L-gct-210/stage3/r14/shapeS2c_%d.sing'%i; open(fn,'w').write('\n'.join(out)+'\n'); print('written',fn)
