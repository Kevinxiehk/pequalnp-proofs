# Round 12: split A for m0 = (1,1,1,1,-4), case (beta): is there a Z (4x5 doubly centred, all five columns isotropic, line C Z with defect in
# C m0, i.e. the t^k coefficients of C_j(tZ) = perm(J_4 + t Z^(j)) satisfy C_1 = C_2 = C_3 = C_0, C_4 = -4 C_0 for k = 3, 4) with NO zero column?
# Charts: column j has a nonzero entry i_j in {0,1,2} (column sums 0); column 0 normalised z[i_0][0] = 1 (scaling of Z), Rabinowitsch for
# the other four columns. Z = 3x4 free block a[i][j] (i < 3, j < 4), last row / last column by the centring.
import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G
def build(chart,p,nz=(1,2,3,4)):
    names=['t']+['a%d%d'%(i,j) for i in range(3) for j in range(4)]+['r%d'%j for j in range(1,5)]
    G.setup(p,len(names)); V=G.var; C=G.const; one=C(1)
    a=[[V(1+4*i+j) for j in range(4)] for i in range(3)]
    i0=chart[0]; a[i0][0]=one                                   # normalise column 0
    Z=[[None]*5 for _ in range(4)]
    for i in range(3):
        for j in range(4): Z[i][j]=a[i][j]
        Z[i][4]=G.lin([(-1,a[i][j]) for j in range(4)])
    for j in range(5): Z[3][j]=G.lin([(-1,Z[i][j]) for i in range(3)])
    eqs=[]
    for j in range(5): eqs.append(G.lin([(1,G.mul(Z[i][j],Z[i][j])) for i in range(4)]))      # isotropic columns
    t=V(0); Cj=[]
    for j in range(5):
        cols=[c for c in range(5) if c!=j]
        M=[[G.add(one,G.mul(t,Z[i][c])) for c in cols] for i in range(4)]; Cj.append(G.perm(M))
    D=[G.sub(Cj[1],Cj[0]),G.sub(Cj[2],Cj[0]),G.sub(Cj[3],Cj[0]),G.sub(G.add(Cj[4],G.scal(4,Cj[0])),C(120))]   # C_4 - 24 = -4 (C_0 - 24)
    for d in D:
        for k,v in G.coeffs(d,[0]).items():
            if v: eqs.append(v)
    for j in nz:                                                # column j: entry chart[j] nonzero
        eqs.append(G.sub(G.mul(V(12+j),Z[chart[j]][j]),one))
    use=[x for x in range(1,len(names)) if not (x==1+4*i0)]
    return names,[e for e in eqs if e],use
if __name__=='__main__':
    import time
    p=int(sys.argv[1]); t0=time.time(); res={}
    for ch in itertools.product(range(3),repeat=5):
        names,eqs,use=build(ch,p); path='/home/kevxhk/work/L-gct-210/stage3/r12/gb_zb_%d_%s.ms'%(p,''.join(map(str,ch)))
        G.write_ms(path,names,eqs,use); r,body=G.msolve(path,timeout=300); res[ch]=r
        if r!='unit': print(ch,'NONUNIT',r,body.replace('\n',' ')[:400],flush=True)
    print('zbeta p',p,'charts',len(res),'unit',sum(1 for v in res.values() if v=='unit'),'time %.0f s'%(time.time()-t0),flush=True)
