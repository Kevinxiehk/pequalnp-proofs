# Round 11, target 2: for each census space whose genuine part is ONE 2-dim skew block (type e=4, g2,skew2), replace the block
# {e_p x + e_q Bx} by its undeformed version {e_p x} and test whether this BASE is again a 6-dim level space (=> the space is a skew
# deformation of a level space, i.e. a member of the deformation table's setting).
import sys, re; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np, glob
from pieces import sub_supported
from ext6 import F45
src=open('/home/kevxhk/work/L-gct-210/reg2/bispan_all.py').read(); files=eval(src.split('files=')[1].split('\n')[0])+sorted(glob.glob('dr35_u*_s*.npy'))
def null(A,tol=1e-9):
    u,s,vh=np.linalg.svd(A); r=int((s>tol*max(1,s[0])).sum()); return vh[r:].conj()
def lin(M):
    L=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; L.append(sub_supported(M,m))
    for c in range(5):
        m=np.zeros((4,5),bool); m[:,c]=True; L.append(sub_supported(M,m))
    L=[l.reshape(len(l),-1) for l in L if len(l)]
    return np.concatenate(L,0) if L else np.zeros((0,20))
def lev(B):
    rg=np.random.default_rng(3); C=rg.normal(size=(30,len(B)))+1j*rg.normal(size=(30,len(B))); return np.abs(F45(np.einsum('nk,kij->nij',C,B))-120).max()
res={'level base':0,'non-level base':0}; bad=[]
for f in files:
    try: M=np.load(f)
    except Exception: continue
    if M.ndim!=3 or M.shape[1:]!=(4,5) or np.linalg.matrix_rank(M.reshape(6,-1) if len(M)==6 else M.reshape(len(M),-1),tol=1e-8)!=6: continue
    M=M/np.abs(M).max()
    if lev(M)>1e-6: continue
    L=lin(M); e=np.linalg.matrix_rank(L,tol=1e-6) if len(L) else 0
    if e!=4: continue
    for kind in ('R','C'):
        n=4 if kind=='R' else 5; done=False
        for p in range(n):
            for q in range(n):
                if p==q or done: continue
                m=np.zeros((4,5),bool)
                if kind=='R': m[p]=True; m[q]=True
                else: m[:,p]=True; m[:,q]=True
                P=sub_supported(M,m)
                if len(P)<2: continue
                X=(P[:,p,:] if kind=='R' else P[:,:,p]); s=X.sum(1)
                c0=null(s[None,:],1e-6) if np.abs(s).max()>1e-6 else np.eye(len(P)); P0=np.einsum('kc,cab->kab',c0,P)
                # genuine 2-dim: P0 modulo Lin has dim 2 and the first-row parts of the genuine part are independent
                Pf=P0.reshape(len(P0),-1)
                if np.linalg.matrix_rank(np.concatenate([L,Pf],0),tol=1e-6)-e!=2: continue
                # base: replace the second-row (column) part of P0 by 0
                Pb=P0.copy()
                if kind=='R': Pb[:,q,:]=0
                else: Pb[:,:,q]=0
                Bb=np.concatenate([L.reshape(-1,4,5),Pb],0); u,s_,vh=np.linalg.svd(Bb.reshape(len(Bb),-1)); Bb=vh[:int((s_>1e-6).sum())].reshape(-1,4,5)
                ok=(len(Bb)==6 and lev(Bb)<1e-6)
                res['level base' if ok else 'non-level base']+=1
                if not ok: bad.append('%s %s(%d->%d) base dim %d lev %.1e'%(f,kind,p,q,len(Bb),lev(Bb)))
                done=True
print(res); [print('  ',b) for b in bad[:12]]
