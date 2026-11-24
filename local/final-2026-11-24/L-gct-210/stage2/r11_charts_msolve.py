# FO2-joint chart test via msolve mod p [NOTES-stage2 R11-2]. Reads the forms F_i (rational nq x nq matrices) from a chart script written by
# r10_FO2J_exact.py (lines "matrix Fi[n][n]=..."), and for every chart of Gr(k, nq) writes an msolve input (variables y, char p, the entries of
# L F_i L^T) and runs msolve -g 2. All charts giving the GB [1] => the closed subvariety {L in Gr(k,nq): F_i|L = 0} of the PROPER Grassmannian has no
# point over F_p-bar, hence (p not dividing denominators) no point over Q-bar (UPDATE 10 argument). Only for FIXED rational parameters.
# usage: r11_charts_msolve.py CHARTSCRIPT k PRIME THREADS [PARAM]   PARAM = name of a parameter appearing polynomially in the forms
#   (then BOTH charts of P^1 are tested: PARAM affine, and tau = 1/PARAM with the forms homogenised; see NOTES R11-2)
import sys, re, itertools, subprocess, os, sympy as sp
src,k,p,th=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]),sys.argv[4]
PAR=sys.argv[5] if len(sys.argv)>5 else None
ps_=sp.Symbol(PAR) if PAR else None; tau=sp.Symbol('tau')
txt=open(src).read()
forms=[]
for mm in re.finditer(r'matrix F(\d+)\[(\d+)\]\[(\d+)\]=([^;]*);',txt):
    n=int(mm.group(2)); vals=[sp.sympify(v.strip().replace('^','**'),locals={PAR:ps_} if PAR else {}) for v in mm.group(4).split(',')]
    if os.environ.get('GAUSS')=='1': vals=[sp.expand(v.subs(sp.I,int(os.environ['SQRTM1']))) for v in vals]
    if os.environ.get('SQRT3'): vals=[sp.expand(v.subs(sp.sqrt(3),int(os.environ['SQRT3']))) for v in vals]
    forms.append(sp.Matrix(n,n,vals))
nq=forms[0].rows
den=1
for F in forms:
    for e in F: den=sp.ilcm(den,sp.fraction(sp.together(e))[1]) if not PAR else den
if PAR:   # build the tau-chart forms: tau^deg * F(1/tau)
    degs=[max([sp.Poly(e,ps_).degree() if e!=0 else 0 for e in F]) for F in forms]
    forms_tau=[(F.applyfunc(lambda e: sp.expand(sp.together(e.subs(ps_,1/tau))*tau**d))) for F,d in zip(forms,degs)]
assert p==0 or den%p!=0, 'bad prime'
print('forms',len(forms),'nq',nq,'k',k,'prime',p,'lcm of denominators',den,flush=True)

def msstr(e,vars_,p):
    """msolve-safe string: integer coefficients reduced mod p (msolve 0.6.5 mis-reads coefficients >= p in mod-p mode; NOTES R13-3)."""
    P=sp.Poly(sp.expand(e),*vars_)
    terms=[]
    for mon,c in P.terms():
        c=sp.Integer(c) if p==0 else sp.Integer(int(c)%p)
        if c==0: continue
        mono='*'.join('%s^%d'%(v,k) if k>1 else str(v) for v,k in zip(vars_,mon) if k>0)
        terms.append(str(c)+('*'+mono if mono else ''))
    return '+'.join(terms) if terms else '0'
ys=[[sp.Symbol('y%d_%d'%(a,b)) for b in range(nq-k)] for a in range(k)]
flat0=[v for row in ys for v in row]
wd='/tmp/stage2_msolve_%d'%os.getpid(); os.makedirs(wd,exist_ok=True)
bad=0; nch=0; failed=0
CASES=[(forms,flat0+([ps_] if PAR else []),'param-affine' if PAR else 'fixed')]+([(forms_tau,flat0+[tau],'tau-chart')] if PAR and os.environ.get('NOTAU')!='1' else [])
for (FORMS,flat,lab) in CASES:
 for S in itertools.combinations(range(nq),k):
     rest=[c for c in range(nq) if c not in S]
     L=sp.zeros(k,nq)
     for a in range(k):
         L[a,S[a]]=1
         for bi,c in enumerate(rest): L[a,c]=ys[a][bi]
     polys=[]
     for F in FORMS:
         P=(L*(F*den)*L.T).applyfunc(sp.expand)
         for a in range(k):
             for b in range(a,k):
                 e=sp.expand(P[a,b])
                 if e!=0: polys.append(e)
     fn=os.path.join(wd,'c.ms'); out=os.path.join(wd,'c.out')
     if os.path.exists(out): os.remove(out)
     with open(fn,'w') as f:
         f.write(','.join(str(v) for v in flat)+'\n'+str(p)+'\n')
         f.write(',\n'.join(msstr(e,flat,p) for e in polys)+'\n')
     r=subprocess.run(['msolve','-g','2','-t',th,'-f',fn,'-o',out],capture_output=True,text=True)
     res=open(out).read().strip() if os.path.exists(out) else 'NO OUTPUT '+r.stderr[-200:]
     body=''.join(l for l in res.splitlines() if not l.startswith('#')); unit = re.sub(r'\s','',body)=='[1]:'
     nch+=1
     if body.strip()=='' or res.startswith('NO OUTPUT'):
         failed+=1; print('FAILED',lab,'chart',S,flush=True); continue
     if not unit:
         bad+=1; print('NONUNIT',lab,'chart',S,'msolve output head:',res[:200].replace('\n',' '),flush=True)
     elif nch%10==0: print('  charts done',nch,flush=True)
print('RESULT msolve charts %s k=%d p=%d: charts %d, non-unit %d, FAILED %d'%(os.path.basename(src),k,p,nch,bad,failed),flush=True)
