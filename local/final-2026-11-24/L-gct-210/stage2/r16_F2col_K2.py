# [K2 = K with the linear conditions q0(k,L3)=0 eliminated: Gr(3,nq-2)]
# F2col FO2-joint on a SUBFAMILY of a ruling, using the kernel reduction [NOTES-stage2 R15-4]:
#   where rank B_c = nq-1 with common kernel C k, every 4-dim common isotropic L'' contains k, so L'' = C k + L3 with L3 a 3-dim subspace of
#   span{e_j : j != i} (i: an index with k_i a nonzero CONSTANT). Equations: G(y_a, y_b) = 0 (all forms G, a <= b), q0(k, y_a) = 0, q0(k, k) = 0.
#   Charts: Gr(3, nq-1) (35 charts for nq = 8, 12 chart variables). Valid only on {rank B_c = nq-1}; the complement {cof_ii(B_c) = 0} is a separate
#   system (full Gr(4,nq) chart run on that lower-dimensional locus).
# usage: r16_F2col_K.py CACHE CH [SUBS e.g. "a1=6-2*a2-2*a3" or "nu=1/2,a2=1/3,a3=2/5,a1=..."]   env: CHARTS, MSV, SAT(=1), EXTRA (extra Rabinowitsch factor)
import sys, itertools, subprocess, os, re, pickle, sympy as sp
from sympy.polys.matrices import DomainMatrix
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())
ck=sys.argv[1]; CH=sys.argv[2]
lam,nu,a1,a2,a3,par,Gs,co,nq,dens,detX,rkjump,fix=pickle.load(open(ck,'rb'))
loc={str(p):p for p in par}; sub={}
if len(sys.argv)>3 and sys.argv[3]:
    for kv in sys.argv[3].split(','):
        k_,v=kv.split('='); sub[sp.Symbol(k_)]=sp.sympify(v,locals=loc)
def S(e): return sp.expand(sp.sympify(e).subs(sub)) if sub else sp.expand(e)
Gs=[G.applyfunc(S) for G in Gs]; par=[p for p in par if p not in sub]
print('subfamily',sub,' remaining parameters',par,' nq',nq,flush=True)
dom=sp.QQ.frac_field(*par) if par else sp.QQ
Bst=sp.Matrix.vstack(*Gs[1:]); rs=DomainMatrix.from_Matrix(Bst).convert_to(dom).rank(); print('rank of B-stack:',rs,flush=True)
assert rs==nq-1, 'common kernel not 1-dim on this subfamily'
k=DomainMatrix.from_Matrix(Bst).convert_to(dom).nullspace().to_Matrix().row(0).applyfunc(sp.cancel)
i=[j for j in range(nq) if k[j]!=0 and sp.sympify(k[j]).is_number][0]; k=k/k[i]
assert all(sp.sympify(x).is_number for x in k), 'kernel vector not constant: generalise'
print('kernel vector k =',list(k),' pivot index',i,flush=True)
G0=Gs[0]; qkk=sp.factor((k*G0*k.T)[0,0]); print('q0(k,k) on the subfamily =',qkk,flush=True)
bad_poly=sp.Integer(1)
if par and os.environ.get('SAT','1')=='1':
    _raw=sp.prod([sp.fraction(sp.together(S(d)))[0] for d in dens])*sp.fraction(sp.together(S(detX)))[0]*sp.fraction(sp.together(S(rkjump)))[0]
    if os.environ.get('EXTRA'): _raw*=sp.sympify(os.environ['EXTRA'],locals=loc)
    _fl=sp.factor_list(sp.expand(_raw),*par)[1]
    bad_poly=sp.expand(sp.prod([f for f,e in _fl if sp.Poly(f,*par).total_degree()>0]) if _fl else 1)
    print('Rabinowitsch polynomial (squarefree):',sp.factor(bad_poly),flush=True)
else:
    for d in dens+[detX]: assert S(d)!=0, 'fixed member lies on an exceptional locus'
EXCL=[f for f,e in sp.factor_list(bad_poly,*par)[1]] if (par and bad_poly!=1) else []
idx=[j for j in range(nq) if j!=i]
# ELIMINATION of the linear conditions q0(k, y) = 0: w = G0 k; pick j0 != i with w_j0 a constant or a product of excluded (Rabinowitsch) factors,
# substitute y_j0 = -(sum_{j != i,j0} w_j y_j) / w_j0 and multiply the bilinear equations by w_j0^2. Charts: Gr(3, nq-2).
w=(G0*k.T).applyfunc(sp.factor); print('w = q0 k =',[str(x) for x in w],flush=True)
j0=None
for j in idx:
    if w[j]==0: continue
    fl=[f for f,e in sp.factor_list(sp.expand(w[j]),*par)[1] if sp.Poly(f,*par).total_degree()>0] if par else []
    if all(any(sp.simplify(f/g).is_number for g in EXCL) for f in fl): j0=j; break
assert j0 is not None, 'no admissible elimination index'
print('eliminating coordinate',j0,'(w_j0 =',w[j0],')',flush=True)
idx2=[j for j in idx if j!=j0]; n7=len(idx2)
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(n7-3)] for r in range(3)]; flat=[v for row in ys for v in row]
wd='/tmp/st2_F2colK_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); bad=0; n=0; failed=0
CHL=[tuple(int(c) for c in x.split('-')) for x in os.environ.get('CHARTS','').split()]
for Sc in (CHL or itertools.combinations(range(n7),3)):
    rest=[c for c in range(n7) if c not in Sc]; Y=sp.zeros(3,nq)
    for r in range(3):
        Y[r,idx2[Sc[r]]]=1
        for bi,c in enumerate(rest): Y[r,idx2[c]]=ys[r][bi]
        Y[r,j0]=-sum(w[j]*Y[r,j] for j in idx2)            # times w_j0: Y row = w_j0 * (true row)  (scaling, w_j0 != 0)
        for j in idx2: Y[r,j]=Y[r,j]*w[j0]
    polys=[]
    for G in (Gs[:1] if os.environ.get('NEGCAL')=='1' else Gs):
        Pm=(Y*G*Y.T).applyfunc(sp.expand)
        for a in range(3):
            for b in range(a,3):
                if Pm[a,b]!=0: polys.append(Pm[a,b])
    for a in range(3):
        e=sp.expand((k*G0*Y.row(a).T)[0,0]); assert e==0, 'elimination failed'
    if sp.expand(qkk)!=0: polys.append(sp.expand(qkk*1))
    vv=flat+par
    if par and bad_poly!=1:
        wv=sp.Symbol('wB'); polys.append(sp.expand(wv*bad_poly-1)); vv=vv+[wv]
    fn=wd+'/c.ms'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    if os.environ.get('ENGINE')=='sing':   # proof-grade in char 0: Singular std over QQ (exact rational arithmetic)
        fn=wd+'/c.sing'
        open(fn,'w').write('ring r=0,(%s),dp;\noption(redSB);\nideal I=%s;\nideal G=std(I);\nwrite(":w %s", string(G));\nquit;\n'%(','.join(str(v) for v in vv),',\n'.join(msstr(q,vv,0) for q in polys),out))
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; Singular -q %s > /dev/null 2>&1'%fn,shell=True)
        fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)
        res=open(out).read() if fresh else 'NOOUT'
        body=res.strip(); unit=re.sub(r'\s','',body)=='1'
    else:
        open(fn,'w').write(','.join(str(v) for v in vv)+'\n'+CH+'\n'+',\n'.join(msstr(q,vv,CH) for q in polys)+'\n')
        subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t 1 -f %s -o %s > /dev/null 2>&1'%(fn,out),shell=True)
        fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)
        res=open(out).read() if fresh else 'NOOUT'
        body=''.join(l for l in res.splitlines() if not l.startswith('#')); unit=re.sub(r'\s','',body)=='[1]:'
    n+=1
    if res=='NOOUT' or body.strip()=='':
        failed+=1; print('FAILED chart',Sc,flush=True); continue
    if not unit: bad+=1; print('NONUNIT chart',Sc,' head:',body[:200],flush=True)
    elif n%10==0: print('  charts done',n,flush=True)
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True)
print('RESULT F2col-K2(elim) %s sub=%s char %s: %d charts, non-unit %d, FAILED %d'%(os.path.basename(ck),sub,CH,n,bad,failed),flush=True)
