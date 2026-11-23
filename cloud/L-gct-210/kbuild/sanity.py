import sys; sys.path.insert(0,'.')
from core import *
rng=np.random.default_rng(3)
e34=np.array([0,0,0,1,-1.]); r=np.array([2,2,2,-3,-3.])
x=sum((rng.normal()+1j*rng.normal())*b for b in Kb); X=x[:3]
v=rng.normal(size=5)+1j*rng.normal(size=5); c=rng.normal()+1j*rng.normal()
t=x+np.outer(e34,v)+c*np.outer(r,np.ones(5))
Xp=X+2*c*np.ones((3,5))
for k in range(1,6):
    f=Pk(Xp,k)-6*c*sum(Pk(np.delete(Xp,j,1),k-1) for j in range(5))+sum((9*c*c-v[j]*v[l])*Pk(np.delete(Xp,[j,l],1),k-2) for j in range(5) for l in range(5) if j!=l)
    print(k,abs(Pk(t,k)-f))
# P2,P3 on m = delta_v + c rho
m=np.outer(e34,v)+c*np.outer(r,np.ones(5)); e2=(v.sum()**2-(v**2).sum())/2
print('P2',abs(Pk(m,2)-(-300*c*c-2*e2)),'P3',abs(Pk(m,3)-(-600*c**3-36*c*e2)))
# K + C E_j level; K + span(E_0,E_1) not
for j in range(5):
    E=np.outer(e34,np.eye(5)[j]); mx=max(abs(Pk(sum((rng.normal()+1j*rng.normal())*b for b in Kb+[E]),k)) for k in range(1,6) for _ in range(2)); print('K+E_%d max|P|'%j,mx)
E0=np.outer(e34,np.eye(5)[0]);E1=np.outer(e34,np.eye(5)[1])
print('E0+E1 P2',Pk(E0+E1,2))
