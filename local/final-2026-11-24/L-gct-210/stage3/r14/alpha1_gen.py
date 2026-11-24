# Round 14: (alpha1) for |supp W| = 2 and 4 (normal form of sec. 34 (D)); all isotropic directions at finite tau (6-point orbit argument).
# A_j = n_j (x) psi_j + eps_j rho e_j (x) f, e_j = chi_2/2 - tau_j chi_3 (unit, orthogonal to n_j = w(tau_j)); Z-gauge psi_0 = 0.
# supp 2: Z = v (e_0 - e_1)^T, n_0 = n_1 = v = w(tv); n_2 = w(t2), n_3 = w(t3).   supp 4: z_j = lam_j w(t_j), lam_0 = 1, n_j = w(t_j).
# usage: python3 -I alpha1_gen.py SUPP SIGNS FCHART
import itertools, sys
supp=int(sys.argv[1]); sg=sys.argv[2]; fch=int(sys.argv[3])
chi=[['1','1','1','1'],['1','I','-1','-I'],['1','-1','1','-1'],['1','-I','-1','I']]
def vec(a,b,c): return ['((%s)*(%s)+(%s)*(%s)+(%s)*(%s))'%(a,chi[1][r],b,chi[2][r],c,chi[3][r]) for r in range(4)]
def pair(x,y): return '(%s)'%'+'.join('(%s)*(%s)'%(x[r],y[r]) for r in range(4))
def w(tt): return vec('1','2*%s'%tt,'-2*(%s)^2'%tt)
def eu(tt): return vec('0','1/2','-%s'%tt)
eps=[1 if ch=='+' else -1 for ch in sg]
fv=['f0','f1','f2']; fco=list(fv); fco[fch]='1'; f=vec(*fco)
psi={0:vec('0','0','0')}
for j in (1,2,3): psi[j]=vec('p%da'%j,'p%db'%j,'p%dc'%j)
s=vec('s1','s2','s3')
if supp==2:
    tv=['tv','tv','t2','t3']; n={j:w(tv[j]) for j in range(4)}; e={j:eu(tv[j]) for j in range(4)}
    z={0:w('tv'),1:['(-%s)'%x for x in w('tv')],2:['0']*4,3:['0']*4}
    extra_unk=['tv','t2','t3']; extra_eq=[]
else:
    n={j:w('t%d'%j) for j in range(4)}; e={j:eu('t%d'%j) for j in range(4)}
    lam=['1','l1','l2','l3']; z={j:['(%s)*%s'%(lam[j],n[j][r]) for r in range(4)] for j in range(4)}
    extra_unk=['t0','t1','t2','t3','l1','l2','l3']
    # moments: sum_j lam_j w(t_j) = 0 (chi-coordinates): sum lam = 0, sum lam t = 0, sum lam t^2 = 0
    extra_eq=['1+l1+l2+l3','t0+l1*t1+l2*t2+l3*t3','t0^2+l1*t1^2+l2*t2^2+l3*t3^2']
unk=[x for j in (1,2,3) for x in ('p%da'%j,'p%db'%j,'p%dc'%j)]+['rho']+[x for k,x in enumerate(fv) if k!=fch]+extra_unk+['q']
As={j:['(%s*%s+(%d)*rho*%s*%s)'%(pair(psi[j],s),n[j][r],eps[j],pair(f,s),e[j][r]) for r in range(4)] for j in range(4)}
out=['ring R=(0,I),(%s,t,s1,s2,s3,mu),dp;'%','.join(unk),'minpoly=I^2+1;','matrix Y[4][5];']
for r in range(4):
    for j in range(4): out.append('Y[%d,%d]=(%s+%s)/2+mu*%s;'%(r+1,j+1,s[r],As[j][r],z[j][r]))
    out.append('Y[%d,5]=-%s-(%s)/2;'%(r+1,s[r],'+'.join(As[j][r] for j in range(4))))
perms=list(itertools.permutations(range(4)))
for jd in range(5):
    cols=[c for c in range(5) if c!=jd]
    out.append('poly C%d='%jd+'+'.join('*'.join('(1+t*Y[%d,%d])'%(r+1,cols[pp[r]]+1) for r in range(4)) for pp in perms)+';')
out.append('list D=C1-C0,C2-C0,C3-C0,C4+4*C0-120; ideal J; int k; int j; matrix M;')
out.append('for(k=1;k<=4;k++){ M=coef(D[k],t*s1*s2*s3*mu); for(j=1;j<=ncols(M);j++){J=J,M[2,j];} } J=simplify(J,2);')
rab='q*rho-1' if supp==2 else 'q*rho*l1*l2*l3-1'
out.append('ring R2=(0,I),(%s),dp; minpoly=I^2+1; ideal J=imap(R,J); J=J,%s%s; ideal G=std(J); "RESULT alpha1-s%d %s f%d size",size(G),"dim",dim(G);'%(','.join(unk),rab,''.join(','+x for x in extra_eq),supp,sg,fch))
out.append('quit;')
fn='/home/kevxhk/work/L-gct-210/stage3/r14/a1s%d_%s_%d.sing'%(supp,sg.replace('+','p').replace('-','m'),fch); open(fn,'w').write('\n'.join(out)+'\n'); print(fn)
