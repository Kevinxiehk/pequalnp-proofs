# P-internal conditions of the R3.2 shape at the CC34 calibration 3-space P = span((e0,0),(e1,0),(0,e2-e3)) [isotropic coords]
import numpy as np, itertools
w=np.exp(2j*np.pi/3); n1=np.array([1,w,w*w]); n2=np.array([1,w*w,w])
def perm(M):
    n=M.shape[0]; return sum(np.prod([M[r,s[r]] for r in range(n)]) for s in itertools.permutations(range(M.shape[1]),n))
E=[np.zeros((3,4),complex) for _ in range(3)]
E[0][:,0]=n1; E[1][:,1]=n1; E[2][:,2]=n2; E[2][:,3]=-n2
z=1; x=-1+1j*np.sqrt(2); y=-1-1j*np.sqrt(2); m=np.array([x,y,z,z])
print('m: sum',abs(m.sum()),' sum sq',abs((m*m).sum()),' zero-free',min(abs(m)))
rng=np.random.default_rng(1); worst=0; lev=0
for trial in range(20):
    c=rng.normal(size=3)+1j*rng.normal(size=3); t=rng.normal()+1j*rng.normal()
    p=sum(ci*Ei for ci,Ei in zip(c,E))
    R=np.array([perm((np.ones((3,4))+t*p)[:,[j for j in range(4) if j!=k]]) for k in range(4)])
    worst=max(worst,abs(m@R)); lev=max(lev,abs(R.sum()-24))
print('max |m.R|',worst,'  max |sum R - 24|',lev)
