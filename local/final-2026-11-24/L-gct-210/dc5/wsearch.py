import sys, itertools, math; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/dc5')
import numpy as np
from weight import pi
reps={'1':[0,1,2,3,4],'2':[1,0,2,3,4],'22':[1,0,3,2,4],'3':[1,2,0,3,4],'32':[1,2,0,4,3],'4':[1,2,3,0,4],'5':[1,2,3,4,0]}
order={'1':1,'2':2,'22':2,'3':3,'32':6,'4':4,'5':5}
def dcdims(sig,tau,N):
    P=np.zeros((25,25))
    for i in range(5):
        for j in range(5): P[i*5+j, sig[i]*5+tau[j]]=1
    z=np.exp(2j*np.pi/N); out={}
    for e in range(N):
        u,s,vh=np.linalg.svd(P-z**e*np.eye(25)); ns=vh[s<1e-9].conj().reshape(-1,5,5)
        if len(ns)==0: continue
        D=pi(ns).reshape(len(ns),25); r=np.linalg.matrix_rank(D,1e-9)
        if r: out[e]=r
    return out
def zero_sum_free(E,N,ks):
    for k in ks:
        for c in itertools.combinations_with_replacement(E,k):
            if sum(c)%N==0: return False
    return True
def best(dims,N,ks):
    keys=sorted(dims); bestv=[0,None]
    def dfs(i,E,val):
        rem=sum(dims[k] for k in keys[i:])
        if val+rem<=bestv[0]: return
        if i==len(keys):
            if val>bestv[0]: bestv[0]=val; bestv[1]=list(E)
            return
        e=keys[i]
        if zero_sum_free(E+[e],N,ks): dfs(i+1,E+[e],val+dims[e])
        dfs(i+1,E,val)
    dfs(0,[],0); return bestv
if __name__=='__main__':
    res=[]
    for a,b in itertools.combinations_with_replacement(reps,2):
        N=math.lcm(order[a],order[b]); dims=dcdims(reps[a],reps[b],N)
        r=[best(dims,N,range(2,m+1)) for m in (3,4,5)]
        res.append((a,b,N,r)); print(a,b,N,'p2p3:',r[0],' P2-4:',r[1],' P2-5:',r[2],flush=True)
