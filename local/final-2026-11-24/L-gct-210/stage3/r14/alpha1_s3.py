# Round 14: (alpha1), |supp W| = 3 = {0,1,2}: W = v l^T, v = chi_1 (special, WLOG by row symmetry), e = chi_2/2 (unit in v^perp);
# A_j = v (x) psi_j + eps_j rho e (x) f (j <= 2, psi_0 = 0 by the Z-gauge), A_3 = n (x) phi + eps_3 rho e3 (x) f, n = w(tau) & e3 = chi_2/2 - tau chi_3
# (chart 'w') or n = chi_3 & e3 = chi_2/2 (chart 'c3'); K = {Y_s + mu Z}, y_j = (s + A_j s)/2 (j <= 3), y_4 = -s - (1/2) sum_j A_j s.
# All defect coefficients in (t, s, mu); Rabinowitsch q l1 (1 + l1) rho = 1. Vectors in chi-coordinates (a,b,c): x = a chi_1 + b chi_2 + c chi_3.
# usage: python3 -I alpha1_s3.py SIGNS FCHART NCHART [run]    e.g. +++- 0 w
import itertools, subprocess, sys
sg=sys.argv[1]; fch=int(sys.argv[2]); nch=sys.argv[3]; run=len(sys.argv)>4
chi=[['1','1','1','1'],['1','I','-1','-I'],['1','-1','1','-1'],['1','-I','-1','I']]
def vec(a,b,c): return ['((%s)*(%s)+(%s)*(%s)+(%s)*(%s))'%(a,chi[1][r],b,chi[2][r],c,chi[3][r]) for r in range(4)]
def pair(x,y): return '(%s)'%'+'.join('(%s)*(%s)'%(x[r],y[r]) for r in range(4))
eps=[1 if ch=='+' else -1 for ch in sg]
fv=['f0','f1','f2']; fco=list(fv); fco[fch]='1'; f=vec(*fco)
v=vec('1','0','0'); e=vec('0','1/2','0')
psi={0:vec('0','0','0'),1:vec('p1a','p1b','p1c'),2:vec('p2a','p2b','p2c')}; phi=vec('ha','hb','hc')
if nch=='w': n=vec('1','2*tau','-2*tau^2'); e3=vec('0','1/2','-tau'); extra=['tau']
else: n=vec('0','0','1'); e3=vec('0','1/2','0'); extra=[]
l=['1','l1','(-1-l1)']
s=vec('s1','s2','s3')
unk=['l1','p1a','p1b','p1c','p2a','p2b','p2c','ha','hb','hc','rho']+[x for k,x in enumerate(fv) if k!=fch]+extra+['q']
As={}
for j in range(3): As[j]=['(%s*%s+(%d)*rho*%s*%s)'%(pair(psi[j],s),v[r],eps[j],pair(f,s),e[r]) for r in range(4)]
As[3]=['(%s*%s+(%d)*rho*%s*%s)'%(pair(phi,s),n[r],eps[3],pair(f,s),e3[r]) for r in range(4)]
out=['ring R=(0,I),(%s,t,s1,s2,s3,mu),dp;'%','.join(unk),'minpoly=I^2+1;','matrix Y[4][5];']
for r in range(4):
    for j in range(4):
        zj='(%s)*%s'%(l[j],v[r]) if j<3 else '0'
        out.append('Y[%d,%d]=(%s+%s)/2+mu*%s;'%(r+1,j+1,s[r],As[j][r],zj))
    out.append('Y[%d,5]=-%s-(%s)/2;'%(r+1,s[r],'+'.join(As[j][r] for j in range(4))))
perms=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[pp[r]]+1) for r in range(4)) for pp in perms)+';')
out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
out.append('for(k=1;k<=4;k++){ M=coef(D[k],t*s1*s2*s3*mu); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} } J=simplify(J,2);')
out.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal J=imap(R,J); J=J,q*l1*(1+l1)*rho-1; ideal G=std(J); "RESULT alpha1-s3 %s f%d %s size",size(G),"dim",dim(G);'%(','.join(unk),sg,fch,nch))
out.append('quit;')
fn='/home/kevxhk/work/L-gct-210/stage3/r14/a1s3_%s_%d_%s.sing'%(sg.replace('+','p').replace('-','m'),fch,nch); open(fn,'w').write('\n'.join(out)+'\n')
print('written',fn)
