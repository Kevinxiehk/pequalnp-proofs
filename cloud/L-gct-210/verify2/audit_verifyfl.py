# verify2 round 5: spot checks for COMPUTE-verifyfl.md (own evaluation of the defect condition; scripts of verifyfl only to build objects)
import sys; sys.path.insert(0,'/home/claude/work/L-gct-210/verifyfl')
import numpy as np, itertools
import di_ext, r4_pr3
P4=list(itertools.permutations(range(4)))
def perm4(A): return sum(A[0,p[0]]*A[1,p[1]]*A[2,p[2]]*A[3,p[3]] for p in P4)
def cvec(Y): return np.array([perm4(1+np.delete(Y,j,axis=1))-24 for j in range(5)])
def defect_in_Cm(B,m,n=150,seed=0):
    """max over fresh random points of the distance of c(Y) from C m (bilinear test: c x m = 0), and the rank of the span of c"""
    rng=np.random.default_rng(seed); B=np.asarray(B,complex); worst=0; C=[]
    for _ in range(n):
        x=rng.normal(size=len(B))+1j*rng.normal(size=len(B)); c=cvec(np.tensordot(x,B,axes=1)); C.append(c)
        worst=max(worst,max(abs(c[i]*m[j]-c[j]*m[i]) for i in range(5) for j in range(i+1,5)))
    s=np.linalg.svd(np.array(C),compute_uv=False)
    return worst,int(np.sum(s>1e-8*max(1,s[0])))
w=np.exp(2j*np.pi/3)
m=np.array([1,w,w*w,0,0])
print('dim ambient_m(m) for m = (1,w,w^2,0,0):',len(di_ext.ambient_m(m)),' for m = (1,2,-3,0,0):',len(di_ext.ambient_m(np.array([1,2,-3,0,0.]))))
print('mperp rows:',di_ext.mperp(m).shape,' max |w.m| =',np.abs(di_ext.mperp(m)@m).max())
one=np.ones(4); chi1=np.array([1,1j,-1,-1j]); chi2=np.array([1,-1,1,-1]); chi3=np.array([1,-1j,-1,1j])
for beta in (np.sqrt(3)/4,-np.sqrt(3)/4):
    for sg in (1,-1):
        xi=sg*np.sqrt(complex(-3/(32*beta)))
        h0=one/4+beta*chi2
        Z=np.outer(h0,m)+np.outer(chi1,[0,xi,-xi,0,0]); Zs=np.outer(chi1,[1,w*w,w,0,0])
        N=np.array([Z,Zs]); err,e=defect_in_Cm(N,m)
        Ns=r4_pr3.Nplane(beta,sg)
        # same plane as the script's?
        M=np.concatenate([N.reshape(2,-1),Ns.reshape(2,-1)]); same=np.linalg.matrix_rank(M,tol=1e-9)==2
        print('A: beta %+.4f xi %s: defect-in-Cm error %.1e, dim of defect span %d, column sums of Z = m: %s, of Zs = 0: %s, equals Nplane: %s'%(
            beta,np.round(xi,4),err,e,np.allclose(Z.sum(0),m),np.allclose(Zs.sum(0),0),same))
# E: m = (1,2,-3,0,0)
m2=np.array([1,2,-3,0,0.]); r=np.sqrt(7); cp=np.array([1,-3+r,2-r,0,0]); cm=np.array([1,-3-r,2+r,0,0])
print('E: c+ sums',cp.sum(),' cubic condition',m2[0]*cp[1]*cp[2]+m2[1]*cp[0]*cp[2]+m2[2]*cp[0]*cp[1])
NV=np.array([np.outer(chi1,cp),np.outer(chi3,cm)]); NI=np.array([np.outer(chi1,[1,-1,0,0,0]),np.outer(chi1,[0,1,-1,0,0])])
for nm,F in (('N_V',NV),('N_I',NI),('span(chi1 c+)',NV[:1]),('span(chi1 (1,w,w^2,0,0))',np.array([np.outer(chi1,[1,w,w*w,0,0])]))):
    err,e=defect_in_Cm(F,m2); print('E: %-26s defect-in-Cm error %.1e, dim of defect span %d'%(nm,err,e))
