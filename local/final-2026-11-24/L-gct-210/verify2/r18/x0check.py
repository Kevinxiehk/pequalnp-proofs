import numpy as np, itertools, sys
x=np.load(sys.argv[1])
v1=np.r_[1,0,x[0:3]]; v2=np.r_[0,1,x[3:6]]; u1=np.array([x[6],x[7],1,0,x[8]]); u2=np.array([x[9],x[10],0,1,x[11]])
w1,w2,t1,t2=x[12:17],x[17:22],x[22:27],x[27:32]
B=[]
for (r0,r1,p,q) in ((0,1,v1,w1),(0,1,v2,w2),(2,3,u1,t1),(2,3,u2,t2)):
    M=np.zeros((4,5),complex); M[r0]=p; M[r1]=q; B.append(M)
B=np.array(B); print('basis svs',np.round(np.linalg.svd(B.reshape(4,-1),compute_uv=False),3))
P=list(itertools.permutations(range(5),4))
def perm_inj(M): return sum(np.prod([M[i,f[i]] for i in range(4)]) for f in P)
def perm4(M): return sum(np.prod([M[i,f[i]] for i in range(4)]) for f in itertools.permutations(range(4)))
rg=np.random.default_rng(31); err=0; Cs=[]
for sc in (0.3,1,4):
    for _ in range(15):
        c=(rg.normal(size=4)+1j*rg.normal(size=4))*sc; Y=np.tensordot(c,B,axes=1)
        err=max(err,abs(perm_inj(np.ones((4,5))+Y)-120)/max(1,np.abs(Y).max())**4)
        Cs.append([perm4(np.ones((4,4))+np.delete(Y,j,axis=1))-24 for j in range(5)])
print('fresh-point level error (rel): %.1e'%err)
sv=np.linalg.svd(np.array(Cs),compute_uv=False); print('defect svs:',np.array2string(sv/sv[0],precision=2))
rk=lambda A: np.linalg.matrix_rank(np.array(A),1e-8)
print('row projection dims:',[rk(B[:,r,:]) for r in range(4)])
print('single-row part dims:',[4-rk(B[:,[i for i in range(4) if i!=r],:].reshape(4,-1).T) for r in range(4)])
print('single-column part dims:',[4-rk(B[:,:,[j for j in range(5) if j!=c]].reshape(4,-1).T) for c in range(5)])
print('dim c(P_a), dim c(P_c):',rk([B[0].sum(0),B[1].sum(0)]),rk([B[2].sum(0),B[3].sum(0)]))
np.set_printoptions(precision=4,suppress=True,linewidth=160)
print('Y_ab rows (v1,w1,v2,w2):\n',np.array([v1,w1,v2,w2])); print('Y_cd rows (u1,t1,u2,t2):\n',np.array([u1,t1,u2,t2]))
