import numpy as np, itertools, math
n=5; w=np.exp(2j*np.pi/3)
B=[]
b=np.zeros((5,5),complex)
for i in range(3): b[i,0]=w**i; b[i,1]=-w**i
B.append(b)
b=np.zeros((5,5),complex)
for i in range(3): b[i,2]=w**(2*i); b[i,3]=-w**(2*i)
B.append(b)
for j in range(4):
    b=np.zeros((5,5),complex); b[3,j]=1; b[3,4]=-1; B.append(b)
b=np.zeros((5,5),complex); b[:,4]=[1,1,1,0,-3]; B.append(b)
def perm(M):
    return sum(np.prod([M[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n)))
rng=np.random.default_rng(1)
def rnd(idx): return sum((rng.normal()+1j*rng.normal())*B[k] for k in idx)
t=rnd(range(7)); print('level err', abs(perm(np.ones((5,5))+t)-120))
d=rnd([0,1]); y=rnd(range(7)); z=rnd(range(7))
r=lambda m:m.sum(1); c=lambda m:m.sum(0)
lhs=(d*np.outer(r(y),c(z))).sum()+(d*np.outer(r(z),c(y))).sum()+4*(d*y*z).sum()
rhs=2*((r(d*y)*r(z)).sum()+(r(y)*r(d*z)).sum())+2*((c(d*y)*c(z)).sum()+(c(y)*c(d*z)).sum())
print('identity lhs, rhs', lhs, rhs, abs(lhs-rhs))
# general check of T3_dc_closed (d DC, y z arbitrary)
def dcproj(m): return m-m.mean(1,keepdims=True)-m.mean(0,keepdims=True)+m.mean()
d=dcproj(rng.normal(size=(5,5))+1j*rng.normal(size=(5,5))); y=rng.normal(size=(5,5)); z=rng.normal(size=(5,5))+1j
T=0
for I in itertools.permutations(range(5),3):
    for J in itertools.permutations(range(5),3):
        T+=d[I[0],J[0]]*y[I[1],J[1]]*z[I[2],J[2]]
S=lambda m:m.sum()
closed=S(d*y)*S(z)+S(y)*S(d*z)+(d*np.outer(r(y),c(z))).sum()+(d*np.outer(r(z),c(y))).sum() \
  -2*((r(d*y)*r(z)).sum()+(r(y)*r(d*z)).sum())-2*((c(d*y)*c(z)).sum()+(c(y)*c(d*z)).sum())+4*(d*y*z).sum()
print('T3 brute', T, 'closed', closed, 'err', abs(T-closed))
