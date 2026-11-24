# Independent check of the (N0)-family generator r9_gen.py against the general T_1 tool (r8_caseB.T1 / r7-style projection):
# build X = C xi_d + X_0 from the family formulas at given parameters, verify level + G = 0, and print dim Omega (row-r projection of T_1).
import sys, numpy as np
A_=list(sys.argv); sys.argv=[A_[0]]
exec(open('/home/kevxhk/work/L-gct-210/stage2/r8_caseB.py').read().split("if __name__=='__main__':")[0])
def fam_pq(fam,par,x):
    x1,x2,x3,x4=x
    if fam=='FM':
        al,be,ga,de,mu=par; pi=al*x3+be*x4; ka=ga*x3+de*x4; sg=x3-2*pi; ta=x4-2*ka
        p=np.array([sg/2+x1,sg/2-x1,pi,pi]); q=np.array([ka,ka,ta/2+x2,ta/2-x2])
    elif fam=='FQ0':
        n1,n2,n3,mu=par; p=np.array([x1,x2,x3,-n1*x1-n2*x2-n3*x3]); u=x4*np.array([n1,n2,n3,1.0]); q=u.sum()-3*u
    elif fam=='FP0':
        al2,al3,al4,mu=par; p=x1*np.array([1,al2,al3,al4]); q=np.zeros(4,complex)
        for i,n in enumerate([[-al2,1,0,0],[-al3,0,1,0],[-al4,0,0,1]]): n=np.array(n,complex); q=q+[x2,x3,x4][i]*(n.sum()-3*n)
    return p,q,mu
def buildfam(fam,par):
    B=[]; M=np.zeros((4,5),complex); M[0,0]=1; M[1,0]=-1; B.append(M)
    for k in range(4):
        x=np.zeros(4); x[k]=1; p,q,mu=fam_pq(fam,par,x); a=p.sum(); b=q.sum(); s=(1-mu)*a+(1+mu)*b
        M=np.zeros((4,5),complex); M[0,0]=s/2; M[1,0]=s/2; M[2,0]=-a-(1+mu)*b; M[2,1:]=p; M[3,0]=(mu-1)*a-b; M[3,1:]=q; B.append(M)
    return np.array(B)
rg=np.random.default_rng(5)
pts=[('FM v=e1 point A (mu=1,de=1/2,al=-1/2)',[-0.5,0,0,0.5,1.0]),('FM v=e1 point B (mu=1,de=-1,al=2/5)',[0.4,0,0,-1.0,1.0]),
     ('FM v=e3 point (mu=-1, 10de^2+de-2=0)',[None]),('FM M1 random', [0.3,0,0,(0.3-1)/(4*0.3-1),0.7]),('FM M3 random',[0.25,-3/16/0.9,0.9,0.25,-0.4])]
de=(-1+np.sqrt(1+80))/20; pts[2]=('FM v=e3 point (mu=-1, de=%.3f)'%de,[-(1+5*de)/3,0,0,de,-1.0])
for name,par in pts:
    B=buildfam('FM',par); print('%-44s err %.1e'%(name,check(B,rg)),end='  '); report('',B)
for name,par in [('FQ0 random n, mu=-1',[0.3+0.2j,-1.1,0.7,-1.0]),('FP0 random al, mu=1',[0.3+0.2j,-1.1,0.7,1.0])]:
    B=buildfam(name[:3],par); print('%-44s err %.1e'%(name,check(B,rg)),end='  '); report('',B)
