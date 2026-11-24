# Round 11, target 2: MECHANISM CENSUS.  For every 6-dim level space of the census: e = dim Lin(M) (span of single-row and single-column
# elements); for every row pair / column pair the piece P and its GENUINE part g* = dim P - dim(P cap Lin(M)); for genuine parts the
# skew rank (rank of the sum-zero part modulo Lin) and nu (a non-sum-zero direction not explained by Lin).  Bi-line span check (BL).
import sys, glob, collections; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
import numpy as np
from pieces import sub_supported
from ext6 import F45
src=open('/home/kevxhk/work/L-gct-210/reg2/bispan_all.py').read(); files=eval(src.split('files=')[1].split('\n')[0])+sorted(glob.glob('dr35_u*_s*.npy'))
def rk(A,tol=1e-6): return np.linalg.matrix_rank(A,tol=tol) if len(A) else 0
def span(A):
    if len(A)==0: return np.zeros((0,20),complex)
    u,s,vh=np.linalg.svd(A.reshape(len(A),-1)); return vh[:int((s>1e-6*max(1,s[0])).sum())]
def inter_dim(A,B):  # dim of intersection of row spaces
    return rk(A)+rk(B)-rk(np.concatenate([A,B],0)) if len(A) and len(B) else 0
sig=collections.Counter(); ex={}; nsp=0; bl_fail=0
for f in files:
    try: M=np.load(f)
    except Exception: continue
    if M.ndim!=3 or M.shape[1:]!=(4,5) or rk(M.reshape(len(M),-1),1e-8)!=6: continue
    M=M/np.abs(M).max(); rg=np.random.default_rng(0); C=rg.normal(size=(20,6))+1j*rg.normal(size=(20,6))
    if np.abs(F45(np.einsum('nk,kij->nij',C,M))-120).max()>1e-6: continue
    nsp+=1
    lines=[]
    for i in range(4):
        m=np.zeros((4,5),bool); m[i]=True; lines.append(sub_supported(M,m))
    for c in range(5):
        m=np.zeros((4,5),bool); m[:,c]=True; lines.append(sub_supported(M,m))
    Lin=span(np.concatenate([l.reshape(len(l),-1) for l in lines if len(l)]+[np.zeros((0,20))],0)); e=len(Lin)
    rows=tuple(len(l) for l in lines[:4]); cols=tuple(len(l) for l in lines[4:])
    parts=[]; pieces=[]
    for (kind,a,b) in [('R',r,j) for r in range(4) for j in range(r+1,4)]+[('C',a,b) for a in range(5) for b in range(a+1,5)]:
        m=np.zeros((4,5),bool)
        if kind=='R': m[a]=True; m[b]=True
        else: m[:,a]=True; m[:,b]=True
        P=sub_supported(M,m)
        if len(P)==0: continue
        Pf=span(P); pieces.append(Pf)
        g=len(Pf)-inter_dim(Pf,Lin) if len(Lin) else len(Pf)
        if g>0:
            # sum-zero part of the genuine piece: sum of the first row (rows) / first column (cols) part
            if kind=='R': s=P[:,a,:].sum(1)
            else: s=P[:,:,a].sum(1)
            if np.abs(s).max()>1e-6:
                u_,s_,vh_=np.linalg.svd(s[None,:]); P0=np.einsum('kc,cab->kab',vh_[1:].conj(),P)
            else: P0=P
            g0=len(span(P0))-inter_dim(span(P0),Lin) if len(Lin) else len(span(P0))
            parts.append('%s%d%d:g%d,skew%d'%(kind,a,b,g,g0))
    Pi=span(np.concatenate(pieces,0)) if pieces else np.zeros((0,20)); bl=len(Pi)
    if bl<6: bl_fail+=1
    key='e=%d rows%s cols%s | %s | BL %d'%(e,''.join(map(str,sorted(rows,reverse=True))),''.join(map(str,sorted(cols,reverse=True))),' '.join(sorted(set(p.split(':')[1] for p in parts))) or '-',bl)
    sig[key]+=1; ex.setdefault(key,(f,parts))
print('spaces:',nsp,'  (BL) failures:',bl_fail)
for k,v in sorted(sig.items(),key=lambda kv:(-int(kv[0].split()[0][2:]),kv[0])): print('%4d  %s   e.g. %s %s'%(v,k,ex[k][0],' '.join(ex[k][1])[:150]))
