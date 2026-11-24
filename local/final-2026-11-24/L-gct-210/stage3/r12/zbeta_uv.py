# Round 12: case (beta) of split A for m0 in the parametrisation z_j = u_j^2 chi_1 + 2 u_j v_j chi_2 - 2 v_j^2 chi_3 (all isotropic vectors of V,
# chi_k = (1, i^k, i^2k, i^3k)); sum z_j = 0 <=> sum u^2 = sum uv = sum v^2 = 0. Line conditions of C Z as in zbeta.py (t-coefficients of
# C_1 - C_0, C_2 - C_0, C_3 - C_0, C_4 + 4 C_0 - 120). Charts: column 0: u_0 = 1 (chart 0) or (u_0 = 0, v_0 = 1) (chart 1); columns 1..4 nonzero
# by Rabinowitsch on u_j (chart 0) or v_j (chart 1).  Mod p, p = 1 mod 4 (i = sqrt(-1) in F_p).
import sys, itertools
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb'); import gbl as G
def build(chart,p,nz=(1,2,3,4)):
    I=next(x for x in range(2,p) if pow(x,(p-1)//4,p)!=1 and (pow(x,(p-1)//4,p)**2+1)%p==0); I=pow(I,(p-1)//4,p); assert (I*I+1)%p==0
    names=['t']+['u%d'%j for j in range(5)]+['v%d'%j for j in range(5)]+['r%d'%j for j in range(1,5)]
    G.setup(p,len(names)); V=G.var; C=G.const; one=C(1); zero={}
    u=[V(1+j) for j in range(5)]; v=[V(6+j) for j in range(5)]
    if chart[0]==0: u[0]=one
    else: u[0]=zero; v[0]=one
    chi=[[pow(I,(k*i)%4,p) for i in range(4)] for k in range(4)]
    Z=[[None]*5 for _ in range(4)]
    for j in range(5):
        a=G.mul(u[j],u[j]); b=G.scal(2,G.mul(u[j],v[j])); c=G.scal(-2,G.mul(v[j],v[j]))
        for i in range(4): Z[i][j]=G.lin([(chi[1][i],a),(chi[2][i],b),(chi[3][i],c)])
    eqs=[G.lin([(1,G.mul(u[j],u[j])) for j in range(5)]),G.lin([(1,G.mul(u[j],v[j])) for j in range(5)]),G.lin([(1,G.mul(v[j],v[j])) for j in range(5)])]
    t=V(0); Cj=[]
    for j in range(5):
        cols=[c_ for c_ in range(5) if c_!=j]
        Cj.append(G.perm([[G.add(one,G.mul(t,Z[i][c_])) for c_ in cols] for i in range(4)]))
    D=[G.sub(Cj[1],Cj[0]),G.sub(Cj[2],Cj[0]),G.sub(Cj[3],Cj[0]),G.sub(G.add(Cj[4],G.scal(4,Cj[0])),C(120))]
    for d in D:
        for k,val in G.coeffs(d,[0]).items():
            if val: eqs.append(val)
    for j in nz: eqs.append(G.sub(G.mul(V(10+j),u[j] if chart[j]==0 else v[j]),one))
    use=[x for x in range(1,len(names)) if not (x==1 or (chart[0]==1 and x==6))]
    return names,[e for e in eqs if e],use
if __name__=='__main__':
    import time
    p=int(sys.argv[1]); only=sys.argv[2] if len(sys.argv)>2 else None; t0=time.time(); res={}
    for ch in itertools.product(range(2),repeat=5):
        tag=''.join(map(str,ch))
        if only and tag!=only: continue
        names,eqs,use=build(ch,p); path='/home/kevxhk/work/L-gct-210/stage3/r12/gb_uv_%d_%s.ms'%(p,tag)
        G.write_ms(path,names,eqs,use); r,body=G.msolve(path,timeout=600); res[ch]=r
        print(tag,'unit' if r=='unit' else 'NONUNIT %s %s'%(r,body.replace('\n',' ')[:300]),'%.1f s'%(time.time()-t0),flush=True)
    print('zbeta_uv p',p,'charts',len(res),'unit',sum(1 for v in res.values() if v=='unit'),flush=True)
