# Round 18: structure of Q-CLOSED 2-row level spaces Y = {(v, Av)} (2-dim, no single-row element): Q(v) = s(v)(v - Av) + 2 v o Av in c(Y) = (I+A)P_a,
# dim c(Y) = 2. Numerical members: look for column structure (a coordinate vector in P_a cap P_b, entries patterns).
import numpy as np, itertools, sys
rg=np.random.default_rng(int(sys.argv[1]))
RB=[rg.normal(size=(5,5))+1j*rg.normal(size=(5,5)) for _ in range(3)]
def unpack(x): return x[0:5],x[5:10],x[10:15],x[15:20]     # Y = span((v1,w1),(v2,w2))
def F(x):
    v1,w1,v2,w2=unpack(x); out=[]
    C=np.stack([v1+w1,v2+w2],1); Pj=np.eye(5)-C@np.linalg.pinv(C)
    for al,be in [(1,0),(0,1),(1,1),(1,-1),(1,2),(2,1j)]:
        v=al*v1+be*v2; w=al*w1+be*w2
        out+=[v.sum()+w.sum(), v.sum()*w.sum()-v@w]
        Q=v.sum()*(v-w)+2*v*w; out+=list(Pj@Q)
    for k,(a,b) in enumerate([(v1,v2),(w1,w2),(v1+w1,v2+w2)]):
        M=np.stack([a,b],1); out.append(x[20+k]*np.linalg.det(M.T@RB[k]@M)-1)
    out.append(np.array([0.3,-0.7,1.1,0.2,0.5])@v1-1); out.append(np.array([1.3,0.4,-0.6,0.9,0.1])@v2-1)
    return np.array(out)
NV=23
def lm(x,it=300):
    lam=1e-2
    for _ in range(it):
        f=F(x); nf=np.linalg.norm(f)
        if nf<1e-12: break
        Jm=np.array([(F(x+1e-7*np.eye(NV)[i])-f)/1e-7 for i in range(NV)]).T
        A=Jm.conj().T@Jm; g=Jm.conj().T@f; ok=False
        for _ in range(10):
            dx=np.linalg.solve(A+lam*np.eye(NV),g)
            if np.linalg.norm(F(x-dx))<nf: x=x-dx; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
    return x,np.linalg.norm(F(x))
found=0
for st in range(25):
    x,nf=lm(rg.normal(size=NV)+1j*rg.normal(size=NV))
    if nf<1e-9:
        found+=1; v1,w1,v2,w2=unpack(x)
        Pa=np.stack([v1,v2]); Pb=np.stack([w1,w2])
        # common vector of P_a and P_b; is it (proportional to) a coordinate vector?
        M=np.concatenate([Pa,-Pb]).T; u,s,vh=np.linalg.svd(M); dimcap=4-np.linalg.matrix_rank(M,1e-7)
        info='dim(P_a cap P_b)=%d'%dimcap
        if dimcap>=1:
            cvec=vh[-1].conj()[:2]@Pa; cvec=cvec/np.abs(cvec).max(); info+=' common vector moduli %s'%np.round(np.abs(cvec),4)
        print('start %d: res %.1e %s'%(st,nf,info),flush=True)
print('found',found)
