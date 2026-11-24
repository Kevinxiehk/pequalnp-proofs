# which case of (I2) does the 3-dim solution fall into?  forms on K: p = a.w, q = b.w, f_u = a.u, g_u = b.u (u in V_012)
import numpy as np, sys
sys.argv=['x','a3','0','0','3']
exec(open('../r8/num/lmH.py').read().split('perms=list')[0])
x=np.load('../r8/num/H_a3_d3_s3_1.npy'); z=x[:len(x)//2]+1j*x[len(x)//2:]; Kc=z[:3*NB].reshape(3,NB); t=z[3*NB:]
KB=np.tensordot(Kc,Bas,axes=(1,0))
w3=np.exp(2j*np.pi/3); n1=np.array([1,w3,w3*w3]); n2=np.array([1,w3*w3,w3])
M=np.vstack([U,t[None,:],np.ones((1,5))]); wv=np.linalg.svd(M)[2][-1].conj(); wv=wv-wv[0]
A_=np.array([KB[i][1:].T@n2/3 for i in range(3)]); B_=np.array([KB[i][1:].T@n1/3 for i in range(3)]); S_=np.array([-KB[i][0] for i in range(3)])
p=A_@wv; q=B_@wv; F=A_@U.T; G=B_@U.T     # columns: forms evaluated on the basis of K
print('p =',np.array2string(p,precision=3),' q =',np.array2string(q,precision=3))
print('rank(p,q) =',np.linalg.matrix_rank(np.vstack([p,q]).T,1e-8))
print('rank of a-part on K:',np.linalg.matrix_rank(A_,1e-8),' b-part:',np.linalg.matrix_rank(B_,1e-8),' s-part:',np.linalg.matrix_rank(S_,1e-8))
print('F (a.u):',np.array2string(F,precision=3)); print('G (b.u):',np.array2string(G,precision=3))
