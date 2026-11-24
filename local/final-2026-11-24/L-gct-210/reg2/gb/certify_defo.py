# Certify FO2 <= 8 on a one-parameter skew deformation (parameter t) of a family member with FIXED integer base parameters (round 8, 16.3).
#   usage: certify_defo.py FAMILY kind idx tgt name=value,...
# Steps: (1) exact sympy basis (t symbolic) from the famtool construction; level identity; generic dim T_1 over Q(t);
#        (2) gen_rank_defo with r = 25 - generic dim T_1 at the fixed parameters (dim T_1 <= generic everywhere, or leftover points);
#        (3) if generic dim T_1 = 10: gcd over all principal 3x3 minors of q_Y on a polynomial kernel basis (rank q >= 3 except its roots);
#        (4) exact certificates (dim T_1, rank q, bound) at all leftover / gcd-root points that are rational.
import sys, subprocess, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2/gb'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/reg2')
import sympy as sp
from famtool import *
fam,kind,idx,tgt,fixs=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
EXTRA=[sp.Rational(x) for x in sys.argv[6].split(',')] if len(sys.argv)>6 else []
FIX=dict(kv.split(':') for kv in fixs.split(',')) if fixs!='-' else {}
src=open('/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank.py').read(); cut=src.index('F=Family(params,bfn,d)')
_ex=EXTRA; sys.argv=['x',fam,'16','1','1']; exec(src[:cut]); EXTRA=_ex
base_bfn=bfn; P0=list(params)
R0=Ring(P0+['t']); Bs=base_bfn(R0,R0.var)
def support(B):
    cells=[(i,j) for i in range(4) for j in range(5) if B[i][j]]; return set(i for i,j in cells), set(j for i,j in cells)
grp=[k for k,B in enumerate(Bs) if (support(B)[1]=={idx} if kind=='col' else support(B)[0]=={idx})]
assert len(grp)==2, grp
syms=sp.symbols(' '.join(P0+['t'])) if len(P0) else (sp.Symbol('t'),)
syms=list(syms) if isinstance(syms,(list,tuple)) else [syms]
sub={sp.Symbol(k):sp.Rational(v) for k,v in FIX.items()}
def tosp(q):
    e=0
    for k,v in q.items():
        term=sp.Integer(v)
        for ex,s in zip(k,syms): term*=s**ex
        e+=term
    return sp.expand(e.subs(sub))
M=[sp.Matrix(4,5,lambda i,j: tosp(B[i][j]) if B[i][j] else 0) for B in Bs]
t=sp.Symbol('t')
v=[M[g][:,idx] if kind=='col' else M[g][idx,:] for g in grp]
g11=(v[0].T*v[0])[0] if kind=='col' else (v[0]*v[0].T)[0]; g12=(v[0].T*v[1])[0] if kind=='col' else (v[0]*v[1].T)[0]; g22=(v[1].T*v[1])[0] if kind=='col' else (v[1]*v[1].T)[0]
J=[g12*v[0]-g11*v[1], g22*v[0]-g12*v[1]]
for n,g in enumerate(grp):
    if kind=='col': M[g][:,tgt]=M[g][:,tgt]+t*J[n]
    else: M[g][tgt,:]=M[g][tgt,:]+t*J[n]
M=[m.applyfunc(sp.expand) for m in M]
ys=sp.symbols('y1:%d'%(len(M)+1))
def perm(A):
    n=A.shape[0]; return sp.Add(*[sp.Mul(*[A[i,p[i]] for i in range(n)]) for p in itertools.permutations(range(n))])
def bigA(Ms,yv=None):
    A=sp.ones(5,5)
    for k,m in enumerate(Ms): A[:4,:]+=(ys[k] if yv is None else yv[k])*m
    return A
lev=sp.expand(perm(bigA(M))-120); print('%s %s %d->%d %s: level identity %s'%(fam,kind,idx,tgt,FIX,lev==0),flush=True)
def fo(Ms):
    A=bigA(Ms); rows={}
    for i in range(5):
        for j in range(5):
            m=A.copy(); m.row_del(i); m.col_del(j); Pp=sp.Poly(sp.expand(perm(m)),*ys[:len(Ms)])
            for mon,cf in Pp.terms(): rows.setdefault(mon,[0]*25); rows[mon][5*i+j]+=cf
    return sp.Matrix(list(rows.values()))
def hess(Ms,yv):
    A=bigA(Ms,yv); H=sp.zeros(25,25)
    for i in range(5):
        for k in range(i+1,5):
            for j in range(5):
                for l in range(5):
                    if j==l: continue
                    m=A.copy(); m.row_del(k); m.row_del(i); cols=[c for c in range(5) if c not in (j,l)]; m=m[:,cols]
                    vv=sp.expand(perm(m)); H[5*i+j,5*k+l]=vv; H[5*k+l,5*i+j]=vv
    return H
A=fo(M); dm=sp.polys.matrices.DomainMatrix.from_Matrix(A).convert_to(sp.QQ.frac_field(t)); n=25-dm.rank()
print('  generic dim T_1 over Q(t) = %d'%n,flush=True)
args=['python3','-I','/home/kevxhk/work/L-gct-210/reg2/gb/gen_rank_defo.py',fam,kind,str(idx),str(tgt),str(25-n),'30','2']+(['fix='+fixs] if fixs!='-' else [])
r=subprocess.run(args,capture_output=True,text=True,timeout=1500); out=' '.join(r.stdout.split()); print('  gen_rank (r=%d): %s'%(25-n,out[out.find('ideal of'):][:300]),flush=True)
pts=set()
if 'COMP' in out:
    for c in out.split('COMP')[1:]:
        c=c.strip()
        try:
            sol=sp.solve(sp.sympify(c.split(',')[0].replace('^','**')),t)
            for s_ in sol:
                if s_.is_rational: pts.add(s_)
                else: print('  NON-RATIONAL leftover point:',c,flush=True)
        except Exception as ex: print('  could not parse leftover',c,ex)
if n==10:
    N=dm.nullspace().to_Matrix(); rows=[]
    for rr in range(N.shape[0]):
        row=[sp.together(e) for e in N.row(rr)]; den=sp.lcm([sp.denom(e) for e in row]); rows.append([sp.expand(sp.cancel(e*den)) for e in row])
    N=sp.Matrix(rows); G=None
    for yv in [(1,2,-1,3,1,-2,1,2,-1),(2,-1,1,1,-3,1,-1,1,2)]:
        H=hess(M,yv[:len(M)]); Q=sp.expand(N*H*N.T)
        for ix in itertools.combinations(range(N.shape[0]),3):
            dd=sp.expand(Q.extract(list(ix),list(ix)).det(method='berkowitz'))
            if dd==0: continue
            G=dd if G is None else sp.gcd(G,dd)
            if sp.degree(G,t)<=0: break
        if G is not None and sp.degree(G,t)<=0: break
    print('  gcd of principal 3x3 minors: %s'%sp.factor(G),flush=True)
    for s_ in sp.solve(G,t):
        if s_.is_rational: pts.add(s_)
        else: print('  NON-RATIONAL gcd root:',s_,flush=True)
elif n>10: print('  generic dim T_1 > 10: needs a separate argument',flush=True)
for p in sorted(set(pts)|set(EXTRA)):
    Mp=[m.subs(t,p) for m in M]; Ap=fo(Mp); Np=Ap.nullspace(); Nm=sp.Matrix.hstack(*Np).T; best=0
    for yv in [(1,2,-1,3,1,-2,1,2,-1),(2,-1,1,1,-3,1,-1,1,2)]:
        H=hess(Mp,yv[:len(Mp)]); best=max(best,(Nm*H*Nm.T).rank())
    print('  point t=%s: dim T_1 = %d, rank q = %d => bound %d'%(p,len(Np),best,len(Np)-(best+1)//2),flush=True)
