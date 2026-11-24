# Round 14: (alpha1), |supp W| = 2 = {0,1}: the PLANE Pi = {s : <psi_1,s> = 0} (psi_0 = 0 gauge, mu = 0) gives a 2-dim subspace {Y_s} of K with
#   y_0 = (s + e0 r<f,s> e_v)/2, y_1 = (s + e1 r<f,s> e_v)/2, y_k = (s + <phi_k,s> n_k + ek r<f,s> e_k)/2 (k = 2,3), y_4 = -s - (1/2) sum_j A_j s,
# rho = 1 (scaling rho <-> f), n = w(tau) and e = chi_2/2 - tau chi_3 for v, n_2, n_3 (all finite: 6-point orbit). Only phi_k|Pi, f|Pi matter.
# Unknowns: Pi (Gr(2,V) chart p,q), phi_2|Pi = (a2,b2), phi_3|Pi = (a3,b3), f|Pi = (g,d), tv, t2, t3.  usage: python3 -I alpha1_s2plane.py SIGNS CHART
import itertools, sys
sg=sys.argv[1]; ch=int(sys.argv[2]); eps=[1 if c=='+' else -1 for c in sg]
chi=[['1','1','1','1'],['1','I','-1','-I'],['1','-1','1','-1'],['1','-I','-1','I']]
def vec(a,b,c): return ['((%s)*(%s)+(%s)*(%s)+(%s)*(%s))'%(a,chi[1][r],b,chi[2][r],c,chi[3][r]) for r in range(4)]
def w(tt): return vec('1','2*%s'%tt,'-2*(%s)^2'%tt)
def eu(tt): return vec('0','1/2','-%s'%tt)
fb=[['1','-1','0','0'],['0','1','-1','0'],['0','0','1','-1']]
ia,ib,ic=[(0,1,2),(0,2,1),(1,2,0)][ch]
sa=['(%s+p*(%s))'%(fb[ia][r],fb[ic][r]) for r in range(4)]; sb=['(%s+q*(%s))'%(fb[ib][r],fb[ic][r]) for r in range(4)]
s=['(x*%s+y*%s)'%(sa[r],sb[r]) for r in range(4)]
fs='(x*g+y*d)'; ph={2:'(x*a2+y*b2)',3:'(x*a3+y*b3)'}
ev=eu('tv'); n2=w('t2'); n3=w('t3'); e2=eu('t2'); e3=eu('t3')
A={0:['(%d)*%s*%s'%(eps[0],fs,ev[r]) for r in range(4)], 1:['(%d)*%s*%s'%(eps[1],fs,ev[r]) for r in range(4)],
   2:['(%s*%s+(%d)*%s*%s)'%(ph[2],n2[r],eps[2],fs,e2[r]) for r in range(4)], 3:['(%s*%s+(%d)*%s*%s)'%(ph[3],n3[r],eps[3],fs,e3[r]) for r in range(4)]}
unk=['p','q','a2','b2','a3','b3','g','d','tv','t2','t3']
out=['ring R=(0,I),(%s,t,x,y),dp;'%','.join(unk),'minpoly=I^2+1;','matrix Y[4][5];']
for r in range(4):
    for j in range(4): out.append('Y[%d,%d]=(%s+%s)/2;'%(r+1,j+1,s[r],A[j][r]))
    out.append('Y[%d,5]=-%s-(%s)/2;'%(r+1,s[r],'+'.join(A[j][r] for j in range(4))))
perms=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[pp[r]]+1) for r in range(4)) for pp in perms)+';')
out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
out.append('for(k=1;k<=4;k++){ M=coef(D[k],t*x*y); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} } J=simplify(J,2);')
out.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal J=imap(R,J); ideal G=std(J); "RESULT alpha1-s2-plane %s chart %d size",size(G),"dim",dim(G);'%(','.join(unk),sg,ch))
out.append('quit;')
fn='/home/kevxhk/work/L-gct-210/stage3/r14/a1s2p_%s_%d.sing'%(sg.replace('+','p').replace('-','m'),ch); open(fn,'w').write('\n'.join(out)+'\n'); print(fn)
