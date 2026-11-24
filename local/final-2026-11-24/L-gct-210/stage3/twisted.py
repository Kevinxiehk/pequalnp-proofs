import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/stage3")
from s3lib import *
# a "twisted full free column" F_5 = {sum c_i e_i rho_i^T : sum c = 0} that is level although rho_1, rho_2 are not unit vectors:
# rho_1 = e_j + t1*iota, rho_2 = e_j + t2*iota, rho_3 = rho_4 = rho_5 = e_j, iota = (1,w,w^2,0,0) (sum 0, iota.iota = 0), j = 4
w=np.exp(2j*np.pi/3); iota=np.array([1,w,w**2,0,0]); j=4; t1,t2=0.7,-1.3+0.4j
rho=np.array([np.eye(5)[j]+t1*iota,np.eye(5)[j]+t2*iota,np.eye(5)[j],np.eye(5)[j],np.eye(5)[j]])
B=[]
for i in range(4):
    M=np.zeros((5,5),complex); M[i]=rho[i]; M[4]=-rho[4]; B.append(M)
B=np.array(B); rng=np.random.default_rng(0)
print('twisted column F_5: dim',rank(B.reshape(4,-1)),' level error %.1e'%levelerr(B,rng,6))
print('  row sums',np.round(rho.sum(1),12),' <rho_i,rho_k> (i!=k) all = s^2:',np.allclose([rho[i]@rho[k] for i in range(5) for k in range(i)],1))
Z=XS(B,rows=[1,2,3,4]); print('  single-row elements in row 0 of F_5:',len(Z),'; contains the full free column:',len(XS(B,cols=[0,1,2,3]))==4)
x=B[0]-B[1]; print('  Q_x != 0 for x^{12}: max |q_T| = %.2f'%max(abs(x[0,a]*x[1,b]+x[0,b]*x[1,a]) for a,b in PAIRS))
