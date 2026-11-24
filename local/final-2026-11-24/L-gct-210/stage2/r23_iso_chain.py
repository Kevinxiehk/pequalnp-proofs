# Isotropic two-row family over Q(i)(t): the chain found at t = 2/3 (ker B1 of rank 5 -> L'' meets the 3-dim kernel W in dim 2; a combination of all
# forms nondegenerate on W allows isotropic dim 1 only) verified GENERICALLY over Q(i)(t), with the exact exceptional t [NOTES-stage2 R23-1].
# Linear algebra over Q(i)[t] done in Singular (ring (0,i),(t),dp; minpoly i^2+1): ranks via det/minors, kernel via syz.
import pickle, subprocess, os, random, sympy as sp
_,_,_,_,_,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r22/cache_iso2row.pkl','rb'))
t=par[0]; I=sp.I
def S(e): return str(sp.expand(e)).replace('**','^').replace('I','i')
def smat(M): return ','.join(S(x) for x in M)
random.seed(4); cw=[random.randint(1,9) for _ in Gs]
L=['ring r=(0,i),(t),dp;','minpoly=i^2+1;','short=0;','option(redSB);',
   'matrix B1[%d][%d]=%s;'%(nq,nq,smat(Gs[1]))]
for k,G in enumerate(Gs): L.append('matrix G%d[%d][%d]=%s;'%(k,nq,nq,smat(G)))
L+=['module K=syz(B1);','K=minbase(K);','int dk=size(K);','print("kernel rank of B1 over Q(i)(t): "+string(dk));',
    'matrix W=transpose(matrix(K));',                        # dk x nq, rows = kernel vectors (polynomial in t)
    'matrix C=%s;'%('+'.join('%d*G%d'%(c,k) for k,c in enumerate(cw))),
    'matrix CW=W*C*transpose(W);','poly dW=det(CW);','print("det of the combination on W: "+string(factorize(dW)));',
    'ideal m5=minor(B1,%d);'%(nq-3),'ideal g5=std(m5);','print("5-minors of B1 vanish only on: "+string(g5));',
    'ideal mw=minor(W,nrows(W));','ideal gw=std(mw);','print("kernel basis degenerates only on: "+string(gw));','quit;']
open('/tmp/st2_isochain.sing','w').write('\n'.join(L)+'\n')
r=subprocess.run('ulimit -v 2000000; timeout 2400 Singular -q /tmp/st2_isochain.sing',shell=True,capture_output=True,text=True)
print(r.stdout[-3000:]); print(r.stderr[-500:])
