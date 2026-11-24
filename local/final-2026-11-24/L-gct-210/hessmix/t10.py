import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/hessmix')
from hk import *
def Phi(x):
    m,a_,b_,g=parts(x); return g-1.5*ab(a_,b_)
def nullcomb(M,tol=1e-9):
    u,s,vh=np.linalg.svd(M); rk=int((s>tol*max(1,s[0])).sum()); return vh[rk:].conj()
def span(rows): 
    rows=np.asarray(rows).reshape(len(rows),-1); return np.linalg.svd(rows)[2][:rank(rows)] if len(rows) else rows
ex=examples()
G=np.eye(25)  # G y = y - (25/9) P_AB y
def Gop(y):
    m,a_,b_,g=parts(y.reshape(5,5)); return (y.reshape(5,5)-(25/9)*ab(a_,b_)).ravel()
for name,B in ex.items():
    Bo=orth(B); l=len(Bo)
    Y=np.array([Phi(b).ravel() for b in Bo])
    R=np.array([y.reshape(5,5).sum(1) for y in Y]); C=np.array([y.reshape(5,5).sum(0) for y in Y])
    # identities check
    eQ=np.abs(Y@Y.T-(5/9)*(R@R.T+C@C.T)).max()
    eT=max(abs((Y[i]*Y[j]*Y[k]).sum()-(1/9)*((R[i]*R[j]*R[k]).sum()+(C[i]*C[j]*C[k]).sum())) for i in range(l) for j in range(l) for k in range(l))
    YA=nullcomb(C.T)@Y if rank(C)<l else np.zeros((0,25))   # C=0
    YB=nullcomb(R.T)@Y if rank(R)<l else np.zeros((0,25))
    YA=span(YA); YB=span(YB)
    P=np.array([a*b for a in YA for b in YB]) if len(YA) and len(YB) else np.zeros((0,25))
    dP=rank(P) if len(P) else 0
    orthP=np.abs(P@Y.T).max() if len(P) else 0
    GY=np.array([Gop(y) for y in Y]); one=np.ones((1,25))
    tot=rank(np.vstack([one,GY]+([P] if len(P) else [])))
    # stabilizer of P: z with z*P subset P  (dimension)
    print(name,'l=%d rA=%d rB=%d d=%d'%(l,rank(R),rank(C),inv(B)['d']),'errQ %.0e errT %.0e'%(eQ,eT),
          '| dimYA=%d dimYB=%d dim(YA*YB)=%d orth(Y)=%.0e | dim(1+GY+YA*YB)=%d <= 25-l=%d ; Kneser lb dimYA+dimYB-1=%d'%(len(YA),len(YB),dP,orthP,tot,25-l,len(YA)+len(YB)-1))
