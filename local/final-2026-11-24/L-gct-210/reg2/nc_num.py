# numerical invariants of the NC line-spanned families (TASK X1', NOTES-reg2 section 11): level error, (dim E_0, dim Omega, dim T_1, FO2),
# Omega basis (rref), deletable rows / neutral columns.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from t import *
from a1 import embed, defect
from a5 import onb
from a6 import T1, E0
from r5_FO2 import FO2
from show import rref
rg=np.random.default_rng(0); w3=np.exp(2j*np.pi/3)
def E(cells):
    m=np.zeros((4,5),complex)
    for (i,j,v) in cells: m[i,j]=v
    return m
def rowel(i,w): m=np.zeros((4,5),complex); m[i]=w; return m
def colel(c,x): m=np.zeros((4,5),complex); m[:,c]=x; return m
def cross3(x):   # x in C^4 with x_0 = 0: the vector (0, x2-x3, x3-x1, x1-x2)
    return np.array([0,x[2]-x[3],x[3]-x[1],x[1]-x[2]],complex)
def perpbasis(vs,n):
    return null(np.array(vs,complex)) if len(vs) else np.eye(n,dtype=complex)
def report(name,B):
    B=np.array(B,complex); Bo=onb(B); le=level_err(Bo,ntest=25)
    if len(Bo)<6 or le>1e-8: print('%-34s dim %d level err %.1e  NOT a 6-dim level space'%(name,len(Bo),le),flush=True); return
    T=T1(embed(Bo),rg,npts=170); U_,S,Vh=np.linalg.svd(T[:,4,:].T,full_matrices=False); r=int((S>1e-8*S[0]).sum())
    R,_=rref(U_[:,:r].T.reshape(r,1,5)); Om=np.round(R.reshape(r,5).real,2)
    fo=FO2(embed(Bo),np.random.default_rng(1),npts=170); e=int((defect(Bo)>1e-8).sum())
    print('%-34s lev %.0e e=%d dimE0=%d dimOmega=%d dimT1=%d FO2=%s Omega=%s'%(name,le,e,len(E0(Bo,rg,npts=170)),r,len(T),fo,Om.tolist()),flush=True)
if __name__=='__main__':
    which=sys.argv[1]
    if which=='321':
        # (3|2,1)(a): U = {w_4 = 0, sum = 0} in row 0, x' in column 3 with x'_0 = 0, V = x'^perp cap 1^perp in column 4
        for p in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0):
            xp=np.array([0,1,p,-1-p],complex); V=[np.array([3,-1,-1,-1],complex),cross3(xp)]
            U=[np.eye(5)[0]-np.eye(5)[k] for k in (1,2,3)]
            report('(3|2,1)a p=%s'%p,[rowel(0,u) for u in U]+[colel(4,v) for v in V]+[colel(3,xp)])
        xp=np.array([0,0,1,-1],complex); V=[np.array([3,-1,-1,-1],complex),cross3(xp)]
        report('(3|2,1)a x=(0,0,1,-1)',[rowel(0,np.eye(5)[0]-np.eye(5)[k]) for k in (1,2,3)]+[colel(4,v) for v in V]+[colel(3,xp)])
        # (b2): U = {w_3 = 0}, V = {x_0 = 0} in column 4, x' = (-3,1,1,1) in column 3
        U=[np.eye(5)[0]-np.eye(5)[k] for k in (1,2,4)]
        report('(3|2,1)b2',[rowel(0,u) for u in U]+[colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1]),colel(3,[-3,1,1,1])])
    if which=='213':
        # (2,1|3): column 4 carries all of 1^perp; u in H_4 (columns 0..3, sum 0) in row 1; U_0 = u^perp cap H_4 in row 0
        for u in ([1,2,-0.5,-2.5,0],[1,-1,0,0,0],[1,1,-2,0,0],[1,1,-1,-1,0],[1,1j,-1,-1j,0],[1,w3,w3**2,0,0],[3,-1,-1,-1,0],[1,0.3+1j,-0.2,-1.1-1j,0]):
            u=np.array(u,complex); H=perpbasis([np.ones(5),np.eye(5)[4],u],5)
            B=[rowel(0,h) for h in H]+[rowel(1,u)]+[colel(4,v) for v in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1])]
            report('(2,1|3) u=%s'%np.round(u,2).tolist(),B)
    if which=='3111':
        U=[np.eye(5)[0]-np.eye(5)[k] for k in (1,2,3)]
        for p in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5):
            x2=np.array([0,1,p,-1-p],complex); x3=cross3(x2)
            report('(3|1,1,1)b-i p=%s'%p,[rowel(0,u) for u in U]+[colel(4,[3,-1,-1,-1]),colel(2,x2),colel(3,x3)])
        x2=np.array([0,0,1,-1],complex); report('(3|1,1,1)b-i x2=(0,0,1,-1)',[rowel(0,u) for u in U]+[colel(4,[3,-1,-1,-1]),colel(2,x2),colel(3,cross3(x2))])
        l=np.array([0,1,w3,w3**2]); report('(3|1,1,1)b-ii',[rowel(0,u) for u in U]+[colel(4,[3,-1,-1,-1]),colel(2,l),colel(3,l)])
        report('(3|1,1,1)b-ii beta=1 (expect NOT level)',[rowel(0,u) for u in U]+[colel(4,np.array([3,-1,-1,-1])+l),colel(2,l),colel(3,l)])
        report('(3|1,1,1)a (expect NOT level)',[rowel(0,u) for u in [np.array([1,2,-0.5,-2.5,0])]]+[rowel(0,u) for u in null(np.array([np.ones(5),[1,2,-0.5,-2.5,0]]))[:2]]+[colel(1,l),colel(2,l),colel(3,l)])
    if which=='2121':
        def U0of(u,zero_cols):   # {w : sum w = 0, w_k = 0 (k in zero_cols), <w,u> = 0}
            return perpbasis([np.ones(5),u]+[np.eye(5)[k] for k in zero_cols],5)
        for s in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5):
            u=np.array([1,s,-1-s,0,0],complex)
            report('(2,1|2,1)V0 s=%s'%s,[rowel(0,h) for h in U0of(u,[3])]+[rowel(1,u),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1]),colel(3,[3,-1,-1,-1])])
        for u in ([1,2,-0.5,-2.5,0],[1,-1,0,0,0],[1,1,-1,-1,0],[1,1j,-1,-1j,0],[3,-1,-1,-1,0],[1,0.3+1j,-0.2,-1.1-1j,0]):
            u=np.array(u,complex)
            report('(2,1|2,1)Vn-i u=%s'%np.round(u,1).tolist(),[rowel(0,h) for h in U0of(u,[4])]+[rowel(1,u),colel(4,[1,-1,0,0]),colel(4,[1,1,-1,-1]),colel(3,[0,0,1,-1])])
        for (s,p) in ((0.3,0.7),(2.0,-0.4+1j),(0.0,0.0),(-1.0,1.0),(-0.5,2.0)):
            u=np.array([1,s,-1-s,0,0],complex); xp=np.array([0,1,p,-1-p],complex)
            report('(2,1|2,1)Vn-ii s=%s p=%s'%(s,p),[rowel(0,h) for h in U0of(u,[4])]+[rowel(1,u),colel(4,[3,-1,-1,-1]),colel(4,cross3(xp)),colel(3,xp)])
    if which=='11121':
        def c3(u): return np.array([u[1]-u[2],u[2]-u[0],u[0]-u[1],0,0],complex)   # orthogonal complement inside H_34 (columns 0,1,2)
        l=np.array([1,w3,w3**2,0,0])
        for s in (0.3,2.0,-0.5+0.7j,1.0):
            u1=np.array([1,s,-1-s,0,0],complex); u2=c3(u1)
            report('(1,1,1|2,1)A1 s=%s'%s,[rowel(0,[1,1,1,0,-3]),rowel(1,u1),rowel(2,u2),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1]),colel(3,[3,-1,-1,-1])])
            for p in (0.7,-1.3+0.5j):
                xp=np.array([0,1,p,-1-p],complex)
                report('(1,1,1|2,1)B1 s=%s p=%s'%(s,p),[rowel(0,[1,1,1,-3,0]),rowel(1,u1),rowel(2,u2),colel(4,[3,-1,-1,-1]),colel(4,cross3(xp)),colel(3,xp)])
        for beta in (0,1):
            report('(1,1,1|2,1)A2 beta=%d'%beta,[rowel(0,np.array([1,1,1,0,-3])+beta*l),rowel(1,l),rowel(2,l),colel(4,[0,1,-1,0]),colel(4,[0,0,1,-1]),colel(3,[3,-1,-1,-1])])
            xp=np.array([0,1,0.7,-1.7],complex)
            report('(1,1,1|2,1)B1iso beta=%d'%beta,[rowel(0,np.array([1,1,1,-3,0])+beta*l),rowel(1,l),rowel(2,l),colel(4,[3,-1,-1,-1]),colel(4,cross3(xp)),colel(3,xp)])
        for (s,q) in ((0.3,0.5),(2.0,-1.0+0.4j),(-0.5,0.0),(1.0,2.0)):
            u2=np.array([1,s,-1-s,0,0],complex); g1=np.array([1,1,1,-3,0],complex); g2=c3(u2); u0=g1+q*g2; u1=(u0@g2)*g1-(u0@g1)*g2
            report('(1,1,1|2,1)B2 s=%s q=%s'%(s,q),[rowel(0,u0),rowel(1,u1),rowel(2,u2),colel(4,[1,-1,0,0]),colel(4,[1,1,-1,-1]),colel(3,[0,0,1,-1])])
    if which=='2211':
        U0=[np.eye(5)[0]-np.eye(5)[1],np.eye(5)[0]-np.eye(5)[2]]; U1=[np.array([-1,-1,-1,4,-1.]),np.array([-1,-1,-1,-1,4.])]
        for p in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5,2+1j):
            x=np.array([1,0,p,-1-p],complex); xp=np.array([x[2]-x[3],0,x[3]-x[0],x[0]-x[2]],complex)   # x' perp x inside {x_1 = 0, sum = 0}
            report('(2,2|1,1)BB p=%s'%p,[rowel(0,u) for u in U0]+[rowel(1,u) for u in U1]+[colel(3,x),colel(4,xp)])
        rg2=np.random.default_rng(3)
        for t in range(6):
            v=rg2.normal(size=5)+1j*rg2.normal(size=5); v-=v.mean()
            if t==4: v=np.array([1,-1,0,0,0],complex)
            if t==5: v=np.array([1,1,-2,0,0],complex)
            U1=[np.array([-1,-1,-1,4,-1],complex),v]; U0=perpbasis([np.ones(5)]+U1,5)
            report('(2,2|1,1)BD #%d'%t,[rowel(0,u) for u in U0]+[rowel(1,u) for u in U1]+[colel(3,[2,0,-1,-1]),colel(4,[0,0,1,-1])])
    if which=='21111':
        report('(2,1|1,1,1)ABD',[rowel(0,[1,-1,0,0,0]),rowel(0,[1,0,0,0,-1]),rowel(1,[1,1,0,-3,1]),colel(2,[1,-3,1,1]),colel(3,[2,0,-1,-1]),colel(4,[0,0,1,-1])])
        for p in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5):
            x2=np.array([0,1,p,-1-p],complex)
            report('(2,1|1,1,1)ACC p=%s'%p,[rowel(0,[1,1,0,-1,-1]),rowel(0,[0,0,0,1,-1]),rowel(1,[1,-1,0,0,0]),colel(2,[3,-1,-1,-1]),colel(3,x2),colel(4,cross3(x2))])
        for s in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5):
            u=np.array([1,s,0,0,-1-s],complex); U0=perpbasis([np.ones(5),np.eye(5)[2],u],5)
            report('(2,1|1,1,1)ACD s=%s'%s,[rowel(0,w) for w in U0]+[rowel(1,u),colel(2,[3,-1,-1,-1]),colel(3,[0,2,-1,-1]),colel(4,[0,0,1,-1])])
    if which=='21111b':
        def c3(u): return np.array([u[1]-u[2],u[2]-u[0],u[0]-u[1],0,0],complex)
        U0=[np.array([-1,-1,-1,4,-1.]),np.array([-1,-1,-1,-1,4.])]
        for (s,p) in ((0.3,0.7),(2.0,-1+0.5j),(-0.5,0.0),(1.0,2.0),(0.0,0.0),(-1.0,1.0)):
            u1=np.array([1,s,-1-s,0,0],complex); x=np.array([0,1,p,-1-p],complex)
            report('(2,1,1|1,1)aa s=%s p=%s'%(s,p),[rowel(0,u) for u in U0]+[rowel(1,u1),rowel(2,c3(u1)),colel(3,x),colel(4,cross3(x))])
        for (s,q) in ((0.3,0.7),(2.0,-1+0.5j),(-0.5,0.0),(1.0,2.0),(0.0,0.0)):
            u1=np.array([1,s,-1-s,0,0],complex); u2=np.array([1,1,1,0,-3],complex)+q*c3(u1); W=perpbasis([np.ones(5),u1,u2],5)
            report('(2,1,1|1,1)ab s=%s q=%s'%(s,q),[rowel(0,w) for w in W]+[rowel(1,u1),rowel(2,u2),colel(3,[0,1,-2,1]),colel(4,[0,1,0,-1])])
        report('(2,1,1|1,1)I-a',[rowel(0,np.eye(5)[0]-np.eye(5)[1]),rowel(0,np.eye(5)[0]-np.eye(5)[2]),rowel(1,[-1,-1,-1,0,3]),rowel(2,[-1,-1,-1,4,-1]),colel(3,[1,-2,0,1]),colel(4,[1,0,0,-1])])
    if which=='21111iso':
        l=np.array([1,w3,w3**2,0,0]); U0=[np.array([1,1,1,-3,0.]),np.array([0,0,0,1,-1.])]
        for p in (0.3,2.0,-0.5+0.7j,0.0,-0.5,1.0):
            x=np.array([0,1,p,-1-p],complex)
            report('(2,1,1|1,1)IV-iso p=%s'%p,[rowel(0,u) for u in U0]+[rowel(1,l),rowel(2,l),colel(3,x),colel(4,cross3(x))])
    if which=='21111II':
        for s in (0.3,2.0,-0.5+0.7j,0.0,1.0,-1.0,-0.5,w3):
            wv=np.array([1,s,-1-s,0,0],complex); U0=perpbasis([np.ones(5),np.eye(5)[3],wv],5)
            report('(2,1,1|1,1)II-2b s=%s'%np.round(s,2),[rowel(0,u) for u in U0]+[rowel(1,wv),rowel(2,[-1,-1,-1,4,-1]),colel(3,[-2,1,0,1]),colel(4,[0,1,0,-1])])
