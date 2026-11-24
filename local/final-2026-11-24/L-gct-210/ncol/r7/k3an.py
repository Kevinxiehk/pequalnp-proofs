# analyse K' hits (3x5 column-centred bases saved by cc3_search.py): isotropic coordinates, product type, defect line m, single-column elements
import sys, numpy as np, itertools
w=np.exp(2j*np.pi/3); n1=np.array([1,w,w*w]); n2=np.array([1,w*w,w])
def iso(Y): return Y.T@n2/3, Y.T@n1/3     # a_j, b_j  (y_j = a_j n1 + b_j n2)
def e2(v): return sum(v[i]*v[j] for i,j in itertools.combinations(range(len(v)),2))
def e3(v): return sum(v[i]*v[j]*v[k] for i,j,k in itertools.combinations(range(len(v)),3))
def dvec(a,b):
    A=a.sum(); B=b.sum(); d2=[]; d3=[]
    for k in range(5):
        ak=np.delete(a,k); bk=np.delete(b,k)
        d2.append(3*((ak*bk).sum()-ak.sum()*bk.sum())); d3.append(6*(e3(ak)+e3(bk)))
    return np.array(d2), np.array(d3)
for f in sys.argv[1:]:
    Bq=np.load(f); D=Bq.shape[0]
    AB=[iso(Y) for Y in Bq]; Am=np.array([x[0] for x in AB]); Bm=np.array([x[1] for x in AB])
    ra=np.linalg.matrix_rank(Am,1e-6); rb=np.linalg.matrix_rank(Bm,1e-6)
    rng=np.random.default_rng(0); V=[]
    for t in range(30):
        c=rng.normal(size=D)+1j*rng.normal(size=D); a=c@Am; b=c@Bm
        d2,d3=dvec(a,b); V+= [d2,d3]
        lev=abs(3*((a*b).sum()-a.sum()*b.sum()))+abs(6*(e3(a)+e3(b)))
    V=np.array(V); s=np.linalg.svd(V,compute_uv=False); e=int((s>1e-6*s[0]).sum()) if s[0]>1e-9 else 0
    m=np.linalg.svd(V)[2][0].conj() if e>0 else np.zeros(5)
    if e>0: m=m/m[np.argmax(abs(m))]
    # single-column elements: kernel of projection onto 4 columns
    sc=[]
    for j in range(5):
        M=np.concatenate([np.delete(Am,j,axis=1),np.delete(Bm,j,axis=1)],1)
        sc.append(D-np.linalg.matrix_rank(M,1e-6))
    zc=[D-np.linalg.matrix_rank(np.concatenate([Am[:,[j]],Bm[:,[j]]],1),1e-6) for j in range(5)]   # dim of elements vanishing in column j
    print(f,': dim',D,' r_a,r_b',ra,rb,' product' if ra+rb==D else ' non-product',' e =',e,' sv',np.array2string(s[:3]/max(s[0],1e-300),precision=1),
          ' m =',np.array2string(m,precision=3),' single-col dims',sc,' zero-col dims',zc,' level resid %.1e'%lev)
