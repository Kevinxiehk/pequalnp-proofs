# Singular generator for Case B(ind) of the (2,4) family, restricted to the three (N0)-families (NOTES-stage2 R9-1).
# Criterion [CRIT] (re-derived in R9-1): (0,v) in Omega  <=>  exists e in C^4, x, y with
#     g_e = 0 on Y_0   and   2 E_v + s (P_e+Q_e) - 2 p_0 Q_e - 2 q_0 P_e + s (x a + y b) = 0 on Y_0      (my normalisation;
# equivalent to r8_gen's 4 E_v + ... since e ranges over a linear space and x, y are free).
#   g_e = sum_j e_j (2 p_j q_j - a q_j - b p_j),  E_v = 2 sum_j v_j p_j q_j + (1-mu) a (2 P_v + Q_v) + (1+mu) b (P_v + 2 Q_v),
#   p_0 = -a-(1+mu) b, q_0 = (mu-1) a - b, s = (1-mu) a + (1+mu) b.
# Omega = C^5 <=> solvable for v = e_1, e_2, e_3 (v = 1' always solvable with e = 0).
# usage: r9_gen.py FAMILY CHAR NV [VLIST]   FAMILY in FP0, FQ0, FM, FMgen ; CHAR = 0 or a prime ; VLIST e.g. 123 (default first NV of 1,2,3)
import sys
fam=sys.argv[1]; ch=sys.argv[2]; NV=int(sys.argv[3]); vl=sys.argv[4] if len(sys.argv)>4 else '123'[:NV]
vl=[int(c) for c in vl]; NV=len(vl)
eqpar=[]
if fam=='FP0':      # pattern p|Y00 = 0  (= stratum S1, mu = 1 forced by (iii)); chart alpha_1 = 1 (WLOG by S_4)
    par=['al2','al3','al4']; mu='1'
    p=['x1','al2*x1','al3*x1','al4*x1']
    ns=[['-al2','1','0','0'],['-al3','0','1','0'],['-al4','0','0','1']]
    # q' = sum_i x_{i+1} * 3 K^{-1} n_i ,  3 K^{-1} n = (sum n) 1 - 3 n
    q=['+'.join('x%d*((%s)-3*(%s))'%(i+2,'+'.join('(%s)'%t for t in ns[i]),ns[i][j]) for i in range(3)) for j in range(4)]
elif fam=='FQ0':    # pattern q|Y00 = 0  (= stratum S3 split, W = 0, mu = -1 forced by (iii)); chart n_4 = 1 (WLOG)
    par=['n1','n2','n3']; mu='-1'
    p=['x1','x2','x3','-n1*x1-n2*x2-n3*x3']
    u=['x4*n1','x4*n2','x4*n3','x4']
    q=['(%s)-3*(%s)'%('+'.join('(%s)'%t for t in u),u[j]) for j in range(4)]
elif fam in ('FM','FMgen'):   # pattern (2,2): S={1,2}, T={3,4}; coordinates x1 = zeta1, x2 = zeta2, x3 = a, x4 = b
    par=['al','be','ga','de']+(['mu'] if fam=='FM' else ['mu']); mu='mu'
    pi='(al*x3+be*x4)'; ka='(ga*x3+de*x4)'; sg='(x3-2*%s)'%pi; ta='(x4-2*%s)'%ka
    p=['(%s/2+x1)'%sg,'(%s/2-x1)'%sg,pi,pi]
    q=[ka,ka,'(%s/2+x2)'%ta,'(%s/2-x2)'%ta]
    eqpar=['ga*(4*al-1)','be*(4*de-1)','1-de-al+4*(al*de+be*ga)']
unk=[]
for i in range(1,NV+1): unk+=['e%d%d'%(i,j) for j in range(1,5)]+['X%d'%i,'Y%d'%i]
mupar=[] if mu in ('1','-1') else []
print('ring R=%s,(%s),dp;'%(ch,','.join(unk+par+['x1','x2','x3','x4'])))
print('option(redSB);')
for j in range(4): print('poly p%d=%s; poly q%d=%s;'%(j+1,p[j],j+1,q[j]))
print('poly mu=%s;'%mu if mu in ('1','-1') else '')
print('poly a=p1+p2+p3+p4; poly b=q1+q2+q3+q4; poly p0=-a-(1+mu)*b; poly q0=(mu-1)*a-b; poly s=(1-mu)*a+(1+mu)*b;')
print('ideal I=%s; matrix C; int k; poly F;'%(','.join(eqpar) if eqpar else '0'))
# sanity: isotropy  a*b - <p',q'> must vanish identically on Y_0 (modulo the parameter equations)
print('poly iso=a*b-(p1*q1+p2*q2+p3*q3+p4*q4); C=coef(iso,x1*x2*x3*x4); ideal ISO; for(k=1;k<=ncols(C);k++){ISO=ISO+ideal(C[2,k]);}')
print('"ISOTROPY CHECK (must be 1):", size(reduce(ISO,std(I)))==0;')
for i,vv in enumerate(vl,1):
    ge='+'.join('e%d%d*(2*p%d*q%d-a*q%d-b*p%d)'%(i,j,j,j,j,j) for j in range(1,5))
    Pe='+'.join('e%d%d*p%d'%(i,j,j) for j in range(1,5)); Qe='+'.join('e%d%d*q%d'%(i,j,j) for j in range(1,5))
    Ev='(2*p%d*q%d+(1-mu)*a*(2*p%d+q%d)+(1+mu)*b*(p%d+2*q%d))'%((vv,)*6)
    Fv='2*%s+s*((%s)+(%s))-2*p0*(%s)-2*q0*(%s)+s*(X%d*a+Y%d*b)'%(Ev,Pe,Qe,Qe,Pe,i,i)
    for F in (ge,Fv):
        print('F=%s; C=coef(F,x1*x2*x3*x4); for(k=1;k<=ncols(C);k++){I=I+ideal(C[2,k]);}'%F)
print('int t=timer; ideal G=std(I); "RESULT %s char %s v=%s: size(std)=",size(G),", unit:",(reduce(1,G)==0), ", dim=",dim(G), ", sec=",timer-t;'%(fam,ch,''.join(map(str,vl))))
print('if(size(G)<=40){G;}')
print('quit;')
