import sys; sys.path.insert(0,"/home/kevxhk/work/L-gct-210/numerics/r2")
from spaces import *
import glob
def hyperplanes(B):
    """yield (label, S) 6-dim subspaces of L=span B cut by structured linear functionals"""
    Q=orth(B); D=len(Q)
    funcs=[]
    for a in range(5):
        for b in range(5):
            f=np.zeros((5,5)); f[a,b]=1; funcs.append((f'e{a}{b}',f))
    for a in range(5):
        f=np.zeros((5,5)); f[a,:]=1; funcs.append((f'row{a}',f))
        f=np.zeros((5,5)); f[:,a]=1; funcs.append((f'col{a}',f))
    for lab,f in funcs:
        v=np.einsum('iab,ab->i',Q,f)
        if np.linalg.norm(v)<1e-9: continue
        # kernel of v on coefficient space
        u,s,vh=np.linalg.svd(v[None]); K=vh[1:].conj()
        yield lab, np.einsum('ij,jab->iab',K,Q)
    for i in range(len(B)):
        yield f'drop{i}', orth(np.delete(B,i,axis=0))
if __name__=="__main__":
    sp={'L080':L080(),'ex1':ex1(),'ex2':ex2(),'ex3':ex3()}
    for f in sorted(glob.glob('F_e2_blk_*.npy'))[:2]: sp[f[:-4]]=np.load(f)
    for nm,B in sp.items():
        seen={}
        for lab,S in hyperplanes(B):
            dS,ES,sS=ext_space(S)
            seen.setdefault(dS,[]).append(lab)
        print(nm, {k:(len(v),v[:6]) for k,v in sorted(seen.items())},flush=True)
