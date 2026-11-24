# Full cube test for all-Type-II triples (everything kappa-free in tau-coordinates): numeric (float) survey.
import sys, itertools, numpy as np; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from pairlib import nullspace, rank, perm
rng=np.random.default_rng(1)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def typeII(cells,eps):
    cells=np.array(cells)
    w=np.where(cells==0,eps*1j,np.where(cells==1,1,-1)).astype(complex)
    return w,(cells==2).astype(float),(cells==1).astype(float),(-1+eps*1j)/2   # w, A_first, A_second, y : A1.tau_i + A2.tau_i' = -y ell
def all_structs():
    out=[]
    for cells in itertools.product(range(3),repeat=5):
        if len(set(cells))<3: continue
        for eps in (1,-1): out.append((cells,eps))
    return out
def opts23(r):
    # r = w3/w2 (complex units up to scalar). find Type II structures: values {a,b,-b}, a = eps*i*b ; Q2=cell(b), Q3=cell(-b)
    vals=[]
    for x in r:
        if not any(abs(x-v)<1e-9 for v in vals): vals.append(x)
    res=[]
    if len(vals)!=3: return res
    for b in vals:
        if any(abs(v+b)<1e-9 for v in vals):
            a=[v for v in vals if abs(v-b)>1e-9 and abs(v+b)>1e-9][0]; eps=int(round((a/(1j*b)).real))
            cells=[0 if abs(x-a)<1e-9 else (1 if abs(x-b)<1e-9 else 2) for x in r]
            res.append((tuple(cells),eps))
    return res
def test(s12,s13,s23,verbose=False):
    w2,A1,A2,y12=typeII(*s12); w3,B1,B3,y13=typeII(*s13); w23,C2,C3,y23=typeII(*s23)
    # functionals on tau (3x5) : rows of N annihilate I_3
    def F(rows): 
        v=np.zeros((3,5),complex)
        for i,vec in rows: v[i]=vec
        return v.reshape(-1)
    one=np.ones(5)
    N=np.array([F([(0,one),(1,-one)]),F([(0,one),(2,-one)]),F([(0,A1+y12*one),(1,A2)]),F([(0,B1+y13*one),(2,B3)]),F([(1,C2+y23*one),(2,C3)])])
    if rank(N)<5: return 'rankN<5'
    I3=nullspace(N); u=np.array([np.ones(5),1/w2,1/w3])
    viol=[]; info=[]
    for S in itertools.combinations(range(5),3):
        Sc=[c for c in range(5) if c not in S]; rows=[i*5+c for i in range(3) for c in Sc]
        K=nullspace(I3[rows,:]); P=I3@K; d=P.shape[1]
        ell=np.concatenate([one,np.zeros(10)])@P
        B1=np.abs(ell).max()>1e-9
        vals=[]
        for _ in range(8):
            cf=rnd(d); tau=(P@cf).reshape(3,5); z=(tau*u)[:,list(S)]; vals.append((perm(z),(ell@cf)**3))
        vals=np.array(vals)
        if B1:
            k=vals[0,0]/vals[0,1]; ok=np.abs(vals[:,0]-k*vals[:,1]).max()<1e-7*max(1,np.abs(vals[:,0]).max())
            if not ok: viol.append(S)
            info.append((S,d,'B1','cube k=%.3f'%abs(k) if ok else 'NOTCUBE'))
        else: info.append((S,d,'ell=0','perm3=0' if np.abs(vals[:,0]).max()<1e-8 else 'perm3!=0'))
    return viol,info
if __name__=='__main__':
    canon=[]
    for comp in ((1,1,3),(1,3,1),(3,1,1),(1,2,2),(2,1,2),(2,2,1)):
        canon.append((tuple([0]*comp[0]+[1]*comp[1]+[2]*comp[2]),1))
    tot=0; surv=[]; stats={}
    for s12 in canon:
        w2=typeII(*s12)[0]
        for s13 in all_structs():
            w3=typeII(*s13)[0]
            for s23 in opts23(w3/w2):
                tot+=1; res=test(s12,s13,s23)
                if res=='rankN<5': stats['rankN<5']=stats.get('rankN<5',0)+1; surv.append((s12,s13,s23,'rankN<5')); continue
                viol,info=res
                if viol: stats['killed']=stats.get('killed',0)+1
                else: stats['SURVIVES']=stats.get('SURVIVES',0)+1; surv.append((s12,s13,s23,info))
    print('all-Type-II triples tested:',tot,stats)
    for s in surv[:12]: print(s[:3]); print('    ',s[3])
