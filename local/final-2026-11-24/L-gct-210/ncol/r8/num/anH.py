import numpy as np, sys
sys.argv=[sys.argv[0]]+sys.argv[1:]
typ=sys.argv[1]; f=sys.argv[2]
exec(open('lmH.py').read().split('perms=list')[0].replace("typ=sys.argv[1]; seed=int(sys.argv[2]); nst=int(sys.argv[3]); DK=int(sys.argv[4]) if len(sys.argv)>4 else 4","typ='%s'; seed=0; nst=0; DK=%d"%(typ,int(sys.argv[3]) if len(sys.argv)>3 else 4)))
x=np.load(f); z=x[:len(x)//2]+1j*x[len(x)//2:]; Kc=z[:DK*NB].reshape(DK,NB); t=z[DK*NB:]
S=Kc[:,:3]                      # s-coordinates (row 0 = -s) of the ker c basis
print('rank of row-0 map on ker c:',np.linalg.matrix_rank(S,1e-8),' singular values',np.array2string(np.linalg.svd(S,compute_uv=False),precision=2))
# rho = rank of the map modulo C*1: s in span(Dp); 1 in span(Dp)? express 1 in Dp basis
one=np.ones(5); c1,*_=np.linalg.lstsq(Dp.T,one,rcond=None)
P=np.eye(3)-np.outer(c1,c1.conj())/np.vdot(c1,c1)
print('rho (rank mod 1):',np.linalg.matrix_rank(S@P.T,1e-8),'  t =',np.array2string(t/t[np.argmax(abs(t))],precision=3))
