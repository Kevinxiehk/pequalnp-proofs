# check the second-order identities (Delta1/Delta2) on the verified 3-dim H solution (type a3): for Y in K, u in U_0:
#   u.R = 0 and 2 u o R + Q u in C, where Q_{jj'} = (2/3) s_j s_j' - 3 (a_j b_j' + a_j' b_j) (j != j'), R = Q 1;
#   rows 1..3 of Y: column j = (s_j/3) 1 + a_j nu1 + b_j nu2, row 0 = -s.
# Also compares with the direct degree-2 part of D_0(Y) u (perm expansion).
import numpy as np, itertools, sys
sys.argv=['x','a3','0','0','3']
src=open('../r8/num/lmH.py').read().split('perms=list')[0]
exec(src)
x=np.load('../r8/num/H_a3_d3_s3_1.npy'); z=x[:len(x)//2]+1j*x[len(x)//2:]; Kc=z[:3*NB].reshape(3,NB); t=z[3*NB:]
KB=np.tensordot(Kc,Bas,axes=(1,0)); Cb=np.vstack([U,t[None,:]])
w3=np.exp(2j*np.pi/3); n1=np.array([1,w3,w3*w3]); n2=np.array([1,w3*w3,w3])
def decomp(Y):
    s=-Y[0]; R3=Y[1:]; a=R3.T@n2/3; b=R3.T@n1/3; return s,a,b
def perm3(M): return sum(M[0,p[0]]*M[1,p[1]]*M[2,p[2]] for p in itertools.permutations(range(3)))
def D0u_deg(Y,u,deg):
    # degree-deg part of D_0(Y)u via scaling: fit polynomial in tau
    taus=np.array([0.3,0.7,1.1,1.6,2.3]); vals=[]
    for tau in taus:
        Yt=tau*Y; v=np.zeros(5,complex)
        for k in range(5):
            for l in range(5):
                if l==k: continue
                cols=[c for c in range(5) if c not in (k,l)]
                v[k]+=u[l]*perm3((1+Yt[1:])[:,cols])
        vals.append(v)
    V=np.array(vals); A=np.vander(taus,5,increasing=True); coef=np.linalg.solve(A,V); return coef[deg]
def inC(v): c,*_=np.linalg.lstsq(Cb.T,v,rcond=None); return np.linalg.norm(v-Cb.T@c)
rng=np.random.default_rng(1); worst=[0,0,0,0]
for _ in range(10):
    c=rng.normal(size=3)+1j*rng.normal(size=3); Y=np.tensordot(c,KB,axes=(0,0)); u=(rng.normal(size=2)+1j*rng.normal(size=2))@U
    s,a,b=decomp(Y)
    Q=(2/3)*np.outer(s,s)-3*(np.outer(a,b)+np.outer(b,a)); np.fill_diagonal(Q,0); R=Q.sum(1)
    d2=D0u_deg(Y,u,2)
    pred=-Q.sum()/2*u+2*u*R-(u@R)*np.ones(5)+Q@u      # Qtot = sum_{j<j'} Q = Q.sum()/2
    worst[0]=max(worst[0],np.linalg.norm(d2-pred)); worst[1]=max(worst[1],abs(u@R)); worst[2]=max(worst[2],inC(2*u*R+Q@u)); worst[3]=max(worst[3],inC(d2))
print('|direct deg-2 - formula| %.1e   |u.R| %.1e   dist(2uoR+Qu, C) %.1e   dist(deg-2 part, C) %.1e'%tuple(worst))
