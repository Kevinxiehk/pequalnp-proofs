# Exact exceptional set of the ONE-STEP chains for the isotropic two-row family over Q(i)(t) [NOTES-stage2 R23-1].
# For a form B_k of generic rank r (nq = 8, L'' dim 4) with kernel W_k (dim d = 8 - r): L'' meets W_k in dim >= 4 - floor(r/2); if a combination C of all
# forms is nondegenerate on W_k, the isotropic dim there is <= floor(d/2). Valid one-step chains: r in {5, 3, 1}. The chain via B_k (and combination c)
# fails at t only if  gcd(r-minors of B_k) * det(C|W_k) * (W_k basis degeneracy)  vanishes. Deg = gcd over all valid (k, c) of these polynomials.
import pickle, subprocess, random, sympy as sp
_,_,_,_,_,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open('/home/kevxhk/work/L-gct-210/stage2/r22/cache_iso2row.pkl','rb'))
def S(e): return str(sp.expand(e)).replace('**','^').replace('I','i')
def smat(M): return ','.join(S(x) for x in M)
random.seed(9); CWS=[[random.randint(1,9) for _ in Gs] for _ in range(2)]
L=['ring r=(0,i),(t),dp;','minpoly=i^2+1;','short=0;','option(redSB);']
for k,G in enumerate(Gs): L.append('matrix G%d[%d][%d]=%s;'%(k,nq,nq,smat(G)))
for j,cw in enumerate(CWS): L.append('matrix C%d=%s;'%(j,'+'.join('%d*G%d'%(c,k) for k,c in enumerate(cw))))
L+=['poly D=0; int nvalid=0; int rk; module K; matrix W; poly f; poly g; ideal mm;',
    'string S="";']
for k in range(1,len(Gs)):
    L+=['K=minbase(syz(G%d)); rk=%d-size(K);'%(k,nq),
        'if(rk==5 or rk==3 or rk==1){',
        '  W=transpose(matrix(K)); mm=minor(G%d,rk); g=std(mm)[1];'%k,
        '  mm=minor(W,nrows(W)); g=g*std(mm)[1];']
    for j in range(len(CWS)):
        L+=['  f=g*det(W*C%d*transpose(W)); if(f!=0){ if(D==0){D=f;} else {D=gcd(D,f);} nvalid++; S=S+"B%d(rank "+string(rk)+",c%d) ";}'%(j,k,j)]
    L+=['}']
L+=['print("valid one-step chains: "+string(nvalid)+" : "+S);','print("Deg = gcd of failure polynomials: "+string(factorize(D)));','quit;']
open('/tmp/st2_isodeg.sing','w').write('\n'.join(L)+'\n')
r=subprocess.run('ulimit -v 2000000; timeout 3000 Singular -q /tmp/st2_isodeg.sing',shell=True,capture_output=True,text=True)
print(r.stdout[-2500:]); print(r.stderr[-400:])
