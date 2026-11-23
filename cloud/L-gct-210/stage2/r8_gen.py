# Singular script generator for Case B (B1) of the (2,4) family: is Omega(X) = C^5 possible?
# Criterion [CRIT] (NOTES R8-2): (0,v) in Omega <=> exists e in C^4, x, y with
#    g_e = 0 on Y_0   and   4 E_v + s (P_e+Q_e) - 2 p_0 Q_e - 2 q_0 P_e - s (x a + y b) = 0 on Y_0.
# Omega = C^5  <=>  solvable for v = e_1, e_2, e_3 (1' is always in).   usage: r8_gen.py STRATUM PRIME NV [extra]  -> Singular script on stdout
import sys
st=sys.argv[1]; prime=sys.argv[2]; NV=int(sys.argv[3]); extra=sys.argv[4] if len(sys.argv)>4 else ''
if st=='S2':
    par=['mu','a13','a14','a23','a24']
    p=['x1','x2','a13*x1+a23*x2','a14*x1+a24*x2']
    n1=['-a13','-a23','1','0']; n2=['-a14','-a24','0','1']
    q=['x3*((1-a13-a23)-3*(%s))+x4*((1-a14-a24)-3*(%s))'%(n1[j],n2[j]) for j in range(4)]
elif st=='S3':
    par=['mu','n1','n2','n3','w12','w13','w23']
    p=['x1','x2','x3','-n1*x1-n2*x2-n3*x3']
    u=['-w12*x2-w13*x3+x4*n1','w12*x1-w23*x3+x4*n2','w13*x1+w23*x2+x4*n3','x4']
    q=['(%s)-3*(%s)'%('+'.join('(%s)'%t for t in u),u[j]) for j in range(4)]
elif st=='S1':
    par=['mu','al2','al3','al4']
    p=['x1','al2*x1','al3*x1','al4*x1']
    ns=[['-al2','1','0','0'],['-al3','0','1','0'],['-al4','0','0','1']]; sg=['1-al2','1-al3','1-al4']
    q=['+'.join('x%d*((%s)-3*(%s))'%(i+2,sg[i],ns[i][j]) for i in range(3)) for j in range(4)]
unk=[]
for i in range(1,NV+1): unk+=['e%d%d'%(i,j) for j in range(1,5)]+['X%d'%i,'Y%d'%i]
print('ring R=%s,(%s),dp;'%(prime,','.join(unk+par+['x1','x2','x3','x4'])))
for j in range(4): print('poly p%d=%s; poly q%d=%s;'%(j+1,p[j],j+1,q[j]))
print('poly a=p1+p2+p3+p4; poly b=q1+q2+q3+q4; poly p0=-a-(1+mu)*b; poly q0=(mu-1)*a-b; poly s=(1-mu)*a+(1+mu)*b;')
print('ideal I; matrix C; int k; poly F;')
if extra: print(extra)
for i in range(1,NV+1):
    ge='+'.join('e%d%d*(2*p%d*q%d-a*q%d-b*p%d)'%(i,j,j,j,j,j) for j in range(1,5))
    Pe='+'.join('e%d%d*p%d'%(i,j,j) for j in range(1,5)); Qe='+'.join('e%d%d*q%d'%(i,j,j) for j in range(1,5))
    Fv='4*(2*p%d*q%d+(1-mu)*a*(2*p%d+q%d)+(1+mu)*b*(p%d+2*q%d))+s*((%s)+(%s))-2*p0*(%s)-2*q0*(%s)-s*(X%d*a+Y%d*b)'%(i,i,i,i,i,i,Pe,Qe,Qe,Pe,i,i)
    for F in (ge,Fv):
        print('F=%s; C=coef(F,x1*x2*x3*x4); for(k=1;k<=ncols(C);k++){I=I+ideal(C[2,k]);}'%F)
print('ideal G=std(I); "RESULT %s prime %s NV %d: size(std)=",size(G),", unit:",(reduce(1,G)==0), ", dim=",dim(G);'%(st,prime,NV))
print('if(size(G)<=12){G;}')
print('quit;')
