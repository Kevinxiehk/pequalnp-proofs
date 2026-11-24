# graded Q-isotropic L (unions of eigenspaces): min over E of dim(L+L∘L) (actual) subject to dim L >= 9
import numpy as np, itertools, sys
sys.path.insert(0,'.')
from core import *
from wgrade import reps, order
def eig_spaces(s,t):
    a,b=order(s),order(t)
    def mat(f): return np.array([to_coords(f(UB[k]))[0] for k in range(24)]).T
    def acts(Um):
        Um=Um.reshape(5,5); V=np.zeros_like(Um)
        for i in range(5): V[s[i],:]=Um[i,:]
        return V.ravel()
    def actt(Um):
        Um=Um.reshape(5,5); V=np.zeros_like(Um)
        for j in range(5): V[:,t[j]]=Um[:,j]
        return V.ravel()
    S=mat(acts); T=mat(actt)
    za=np.exp(2j*np.pi/a); zb=np.exp(2j*np.pi/b)
    sp={}
    for x in range(a):
        for y in range(b):
            P=sum(za**(-x*k)*zb**(-y*m)*np.linalg.matrix_power(S,k)@np.linalg.matrix_power(T,m) for k in range(a) for m in range(b))/(a*b)
            d=int(round(np.trace(P).real))
            if d: sp[(x,y)]=orth(P.T)  # rows span image (coords)
    return a,b,sp
if __name__=='__main__':
  names=list(reps); res=[]
  for i1 in range(len(names)):
    for i2 in range(i1,len(names)):
        s,t=reps[names[i1]],reps[names[i2]]
        a,b,sp=eig_spaces(s,t)
        dims={e:len(v) for e,v in sp.items()}
        neg=lambda e:((-e[0])%a,(-e[1])%b)
        add=lambda e,f:((e[0]+f[0])%a,(e[1]+f[1])%b)
        cand=[e for e in dims if add(e,e)!=(0,0)]
        pairs=[];seen=set()
        for e in cand:
            if e in seen: continue
            seen.add(e); seen.add(neg(e)); pairs.append((e,neg(e)) if neg(e) in dims else (e,))
        best=(99,None)
        for choice in itertools.product(*[range(len(p)+1) for p in pairs]):
            E=[p[c-1] for p,c in zip(pairs,choice) if c]
            v=sum(dims[e] for e in E)
            if v<9: continue
            Es=set(E); S2=Es|{add(x,y) for x in E for y in E}
            bound=sum(dims.get(e,0) for e in S2)
            if bound<best[0]+3:
                Lc=np.vstack([sp[e] for e in E]); Lu=to_mat(Lc)
                g=growth(Lu)[2]
                if g<best[0]: best=(g,E,v,bound)
        print(names[i1],names[i2],'min dim(L+L∘L) over graded iso L, dim>=9:',best,flush=True)
