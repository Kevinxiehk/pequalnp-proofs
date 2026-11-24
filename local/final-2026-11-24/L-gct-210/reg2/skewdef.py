# Round 7: SKEW DEFORMATIONS of line-spanned 6-dim level spaces (NOTES-reg2 15.2).  For a 2-dim single-column part V (x) e_a of M (V a 2-dim
# space of column vectors) and another column b, replace V (x) e_a by { x e_a^T + t (J x) e_b^T : x in V }, J = the generator of so(V) for the
# bilinear form (<x, Jx'> = -<Jx, x'>, defined when V is nondegenerate); likewise for a 2-dim single-row part e_i (x) W coupled to a row j.
# Report which deformations stay level (random t) and the invariants of the deformed spaces.
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, itertools
from a5 import onb
from t import level_err, rank, null, rowpart, colpart
rg=np.random.default_rng(1)
def skewJ(Vb):
    # Vb: 2 x n basis; return J (2x2 in this basis) with G J + (G J)^T = 0, G = Gram (bilinear); J = G^{-1} [[0,1],[-1,0]]
    G=Vb@Vb.T
    if abs(np.linalg.det(G))<1e-9: return None
    return np.linalg.solve(G,np.array([[0,1],[-1,0]]))
def complement(B,P):
    # basis of B modulo span(P) (B, P orthonormal-ish arrays of shape (k,4,5))
    Bf=B.reshape(len(B),-1); Pf=P.reshape(len(P),-1)
    Q=np.linalg.qr(Pf.conj().T)[0]          # orthonormal (hermitian) basis of span P
    R=Bf-(Bf@Q.conj())@Q.T                  # remove components (hermitian projection)
    u,s,vh=np.linalg.svd(R,full_matrices=False); r=int((s>1e-8*s[0]).sum()) if s[0]>1e-12 else 0
    return vh[:r].reshape(r,4,5)
def deformations(name,B):
    B=onb(np.asarray(B,complex)); out=[]
    for a in range(5):
        P=colpart(B,[a])
        if len(P)!=2: continue
        Vb=P[:,:,a]; J=skewJ(Vb)
        if J is None: continue
        rest=complement(B,P)
        for b in range(5):
            if b==a: continue
            t=0.7+0.4j; JVb=(J.T@Vb)          # rows: images of the basis vectors (J acts on coefficient vectors)
            Bl=[]
            for k in range(2):
                m=np.zeros((4,5),complex); m[:,a]=Vb[k]; m[:,b]=t*JVb[k]; Bl.append(m)
            Bd=np.concatenate([rest,np.array(Bl)],0); le=level_err(onb(Bd),ntest=20)
            out.append(('col',a,b,le))
    for i in range(4):
        P=rowpart(B,[i])
        if len(P)!=2: continue
        Wb=P[:,i,:]; J=skewJ(Wb)
        if J is None: continue
        rest=complement(B,P)
        for j in range(4):
            if j==i: continue
            t=0.7+0.4j; JWb=(J.T@Wb); Bl=[]
            for k in range(2):
                m=np.zeros((4,5),complex); m[i]=Wb[k]; m[j]=t*JWb[k]; Bl.append(m)
            Bd=np.concatenate([rest,np.array(Bl)],0); le=level_err(onb(Bd),ntest=20)
            out.append(('row',i,j,le))
    ok=[o for o in out if o[3]<1e-8]
    print('%-30s tried %d deformations, LEVEL: %s'%(name,len(out),[(k,x,y) for (k,x,y,le) in ok]),flush=True)
    return ok
if __name__=='__main__':
    from nc_num import rowel, colel, cross3, perpbasis
    from dr211b_num import fam as f211, member_g, cross4
    from dr22_num_lib import fam22
    from p312_lib import fam as f312
    from dr211iii_num_lib import fam as f211iii
    a,b,c=member_g(rg); deformations('(2,1,1|2)(ii) generic',f211(a,b,c))
    deformations('(2,1,1|2)(iii) generic',f211iii(0.3+0.1j,-0.7))
    deformations('(2,2|2) generic',fam22(0.3+0.2j,-1.1))
    deformations('(3,1|2) generic m',f312(np.array([1,2,-0.5,-2.5,0],complex)))
    u=np.array([1,2,-0.5,-2.5,0],complex); H=perpbasis([np.ones(5),np.eye(5)[4],u],5)
    deformations('(2,1|3)',[rowel(0,h) for h in H]+[rowel(1,u)]+[colel(4,v) for v in ([1,-1,0,0],[0,1,-1,0],[0,0,1,-1])])
    xp=np.array([0,1,0.3,-1.3],complex)
    deformations('(3|2,1)a',[rowel(0,np.eye(5)[0]-np.eye(5)[k]) for k in (1,2,3)]+[colel(4,[3,-1,-1,-1]),colel(4,cross3(xp)),colel(3,xp)])
    deformations('(3|3)',[rowel(0,np.eye(5)[0]-np.eye(5)[k]) for k in (1,2,3)]+[colel(4,[1,-1,0,0]),colel(4,[1,0,-1,0]),colel(4,[1,0,0,-1])])
    U0=[np.eye(5)[0]-np.eye(5)[1],np.eye(5)[0]-np.eye(5)[2]]; U1=[np.array([-1,-1,-1,4,-1.]),np.array([-1,-1,-1,-1,4.])]
    x=np.array([1,0,0.3,-1.3],complex); x2=np.array([x[2]-x[3],0,x[3]-x[0],x[0]-x[2]])
    deformations('(2,2|1,1)BB',[rowel(0,w) for w in U0]+[rowel(1,w) for w in U1]+[colel(3,x),colel(4,x2)])
    w0,w1,w3=np.array([1,-1,0,0.]),np.array([0,0,1,-1.]),np.array([1,1,-1,-1.])
    deformations('NC (1,1,1|3)',[colel(0,[1,-1,0,0]),colel(0,[0,1,-1,0]),colel(0,[0,0,1,-1]),rowel(0,np.r_[0,w0]),rowel(1,np.r_[0,w1]),rowel(3,np.r_[0,w3])])
