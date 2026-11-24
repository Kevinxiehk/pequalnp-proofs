# test the derived a3 identities on the verified 3-dim H solution:
#  (I1) 6X + (8/3)(S s - s o s) + gamma 1  in  C t''   (X = B a + A b - 2 a o b, gamma = 2 Qtot - 2 (S^2 - |s|^2))
#  (I2) (b.u)(a.w) + (a.u)(b.w) = 0 for u in V_012, w = (0,0,0,mu,nu) spanning C^perp mod 1
import numpy as np, sys
sys.argv=['x','a3','0','0','3']
exec(open('../r8/num/lmH.py').read().split('perms=list')[0])
x=np.load('../r8/num/H_a3_d3_s3_1.npy'); z=x[:len(x)//2]+1j*x[len(x)//2:]; Kc=z[:3*NB].reshape(3,NB); t=z[3*NB:]
KB=np.tensordot(Kc,Bas,axes=(1,0))
w3=np.exp(2j*np.pi/3); n1=np.array([1,w3,w3*w3]); n2=np.array([1,w3*w3,w3])
# w: orthogonal (bilinear) to U and t and 1, normalised w_0 = w_1 = w_2 = 0 (it is constant there)
M=np.vstack([U,t[None,:],np.ones((1,5))]); wv=np.linalg.svd(M)[2][-1].conj(); wv=wv-wv[0]
print('w (normalised) =',np.array2string(wv/np.max(abs(wv)),precision=4))
tpp=t-(t[:3].mean())*np.array([1,1,1,0,0])*0   # t'' = t itself (C = U (+) C t)
rng=np.random.default_rng(3); e1=e2=0
for _ in range(10):
    c=rng.normal(size=3)+1j*rng.normal(size=3); Y=np.tensordot(c,KB,axes=(0,0))
    s=-Y[0]; a=Y[1:].T@n2/3; b=Y[1:].T@n1/3; S=s.sum(); A=a.sum(); B=b.sum()
    X=B*a+A*b-2*a*b
    Q=(2/3)*np.outer(s,s)-3*(np.outer(a,b)+np.outer(b,a)); np.fill_diagonal(Q,0); Qt=Q.sum()/2
    gam=2*Qt-2*(S**2-(s*s).sum())
    v=6*X+(8/3)*(S*s-s*s)+gam*np.ones(5)
    cc,*_=np.linalg.lstsq(t[:,None],v,rcond=None); e1=max(e1,np.linalg.norm(v-t*cc[0])/max(1,np.linalg.norm(v)))
    for uu in U:
        e2=max(e2,abs((b@uu)*(a@wv)+(a@uu)*(b@wv)))
print('I1 rel. dist to C t: %.1e    I2 max: %.1e'%(e1,e2))
