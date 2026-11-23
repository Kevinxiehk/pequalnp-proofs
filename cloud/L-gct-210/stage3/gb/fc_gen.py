# Round 8, section 27: F4b, FREE-COLUMN SUB-FAMILY (y_r = e_1, p = -e_1 + p').  Exact system mod p on charts.
# vectors in H_3 = {zero-sum vectors of C^4 (columns N = 2..5)}: q_a,q_b,q_c,q_d,w,p'  (3 free coordinates each, 4th = -sum)
# usage: python3 -I fc_gen.py PRIME MODE   MODE: LEVEL (calibration, must be non-unit) | FULL (level + (i'),(ii'),(iii')) | IDENT23 (level + (ii'),(iii') only)
import sys, itertools, time
sys.path.insert(0,'/home/claude/work/L-gct-210/stage3/gb'); import gbl as G
p=int(sys.argv[1]); MODE=sys.argv[2]
NV=18+7+2; G.setup(p,NV)
names=['%s%d'%(n,i) for n in ('qa','qb','qc','qd','w','pp') for i in range(3)]+['ca','cb','cc','cd','mu','ga','de','tb','td']
PAR=list(range(18,25)); TB,TD=25,26
def vec(k,fix=None):      # fix = (index, value): chart normalisation
    v=[G.var(3*k+i) for i in range(3)]
    if fix is not None: v[fix[0]]=G.const(fix[1])
    v.append(G.lin([(-1,x) for x in v])); return v
def system(ia,ib,ic,id_,iw):
    qa=vec(0,(ia,1)); qb=vec(1); qc=vec(2,(ic,1)); qd=vec(3); w=vec(4,(iw,1)); pp=vec(5)
    used=[i for i in range(18) if i not in (0*3+ia,2*3+ic,4*3+iw)]
    ca,cb,cc,cd,mu,ga,de=[G.var(i) for i in PAR]; sig=G.lin([(1,ca),(1,cb),(1,cc),(1,cd)]); one=G.const(1)
    M=[[G.add(one,ca)]+[G.add(one,G.mul(ga,x)) for x in qa],
       [G.add(one,cb)]+[G.add(one,G.mul(ga,x)) for x in qb],
       [G.add(one,cc)]+[G.add(one,G.mul(de,x)) for x in qc],
       [G.add(one,cd)]+[G.add(one,G.mul(de,x)) for x in qd],
       [G.sub(one,sig)]+[G.lin([(1,one),(1,G.mul(sig,pp[j])),(1,G.mul(mu,w[j]))]) for j in range(4)]]
    f=G.sub(G.perm(M),G.const(120))
    eqs=[v for k,v in G.coeffs(f,PAR).items()]
    nlev=len([e for e in eqs if e])
    if MODE in ('FULL','IDENT23'):
        tr=[]
        if MODE=='FULL':
            Q=[qa,qb,qc,qd]
            for T in itertools.combinations(range(4),3): tr+=list(G.subperms([Q[i] for i in T],3,4).values())
            tr.append(G.perm([qa,qb,qc,qd]))
        for (x,y) in ((qa,qb),(qc,qd)):
            for z in (w,pp): tr+=list(G.subperms([x,y,z],3,4).values())
        eqs+=tr
    # hinges: q_b != 0 (coordinate ib), q_d != 0 (coordinate id_)
    eqs.append(G.sub(G.mul(G.var(TB),qb[ib]),one)); eqs.append(G.sub(G.mul(G.var(TD),qd[id_]),one))
    # gauge: p' -> p' + alpha w, so p'_{iw} = 0
    eqs.append(pp[iw])
    return eqs,used+[TB,TD],nlev
if __name__=='__main__':
    t0=time.time(); res={}
    charts=list(itertools.product([0],range(3),range(3),range(3),range(3)))
    for ch in charts:
        eqs,use,nlev=system(*ch); path='/home/claude/work/L-gct-210/stage3/gb/fc_%s_%d_%s.ms'%(MODE,p,''.join(map(str,ch)))
        n=G.write_ms(path,names,eqs,use); r,body=G.msolve(path); res[ch]=r
        if r!='unit' and len(body)<1500: print(ch,r,body.replace('\n',' ')[:1400])
    print('prime',p,'MODE',MODE,': charts',len(charts),' level equations',nlev,' unit ideals',sum(1 for v in res.values() if v=='unit'),
          ' non-unit',{k:v for k,v in res.items() if v!='unit'},' time %.1f s'%(time.time()-t0))
