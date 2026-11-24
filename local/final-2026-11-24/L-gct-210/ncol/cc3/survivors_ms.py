# independent engine check of the CC3 survivor systems: write msolve files mod p (coefficients reduced mod p) and run msolve
import sympy as sp, sys, subprocess, os
exec(open('survivors.py').read().split("c,k,sa_,sb_=sp.symbols('c k sa sb')")[0])   # reuse helpers (e3, z)
P=int(sys.argv[1]); out=[]
def write_run(name, eqs, unknowns):
    names=','.join(str(u) for u in unknowns)
    lines=[]
    for e in eqs:
        pol=sp.Poly(sp.expand(e),*unknowns)
        terms=[]
        for mon,cf in pol.terms():
            cf=sp.Rational(cf); num=int(cf.p)%P; den=int(cf.q)%P; v=num*pow(den,P-2,P)%P
            if v==0: continue
            mono='*'.join(('%s^%d'%(u,k) if k>1 else str(u)) for u,k in zip(unknowns,mon) if k)
            terms.append(str(v)+('*'+mono if mono else ''))
        if terms: lines.append('+'.join(terms))
    fn='ms_%s_%d.ms'%(name,P)
    open(fn,'w').write(names+'\n%d\n'%P+',\n'.join(lines)+'\n')
    if os.path.exists(fn+'.out'): os.remove(fn+'.out')
    r=subprocess.run(['bash','-c','ulimit -v 2000000; timeout 300 msolve -g 2 -t 1 -f %s -o %s.out'%(fn,fn)],capture_output=True)
    if r.returncode!=0 or not os.path.exists(fn+'.out') or os.path.getmtime(fn+'.out')<os.path.getmtime(fn):
        print(name,P,'FAILED rc=%d'%r.returncode,flush=True); return
    res=open(fn+'.out').read(); print(name,P,'UNIT' if res.split('#---')[-1].strip().startswith('[1]') else 'NONUNIT', flush=True)
def build(name, ahat, bhat, unknowns, extra):
    sa=sum(ahat); sb=sum(bhat)
    a=[sp.expand(x-sa/3) for x in ahat]; b=[sp.expand(x-sb/3) for x in bhat]
    F3=sp.expand(e3(a)+e3(b))
    d3=[sp.expand(e3([a[k] for k in range(5) if k!=j])+e3([b[k] for k in range(5) if k!=j])) for j in range(5)]
    eqs=list(extra)
    for E in [F3, d3[0]-d3[1], d3[0]-d3[2], d3[0]-d3[3]]: eqs+=sp.Poly(E,*z).coeffs()
    write_run(name,[e for e in eqs if sp.expand(e)!=0],unknowns)
c,k,sa_,sb_,inv,sbb=sp.symbols('c k sa sb inv sbb')
u=sp.symbols('u0:8')
f=[z3+u[0]*z1+u[1]*z2, -z3+u[2]*z1+u[3]*z2, z4+u[4]*z1+u[5]*z2, -z4+u[6]*z1+u[7]*z2]
ahat=f+[k*z1]; bhat=[0,0,0,0,sb_*z2]
extra=[sp.expand(sb_*k-5*c)]+sp.Poly(sp.expand(sum(ahat))-sa_*z1,*z).coeffs()+[sp.expand(sa_*sb_-9*c), sp.expand(inv*k*c-1)]
build('s40',ahat,bhat,list(u)+[k,c,sa_,sb_,inv],extra)
v=sp.symbols('v0:4'); w=sp.symbols('w0:4')
fA=[z3+v[0]*z1+v[1]*z2, -z3+v[2]*z1+v[3]*z2]; gB=[z4+w[0]*z1+w[1]*z2, -z4+w[2]*z1+w[3]*z2]
for o in (0,1):
    ap=k*z1 if o==0 else k*z2; bp=sb_*z2 if o==0 else sb_*z1
    ahat=[fA[0],fA[1],0,0,ap]; bhat=[0,0,gB[0],gB[1],bp]
    extra=[sp.expand(sb_*k-5*c)]+sp.Poly(sp.expand(sum(ahat))-sa_*z1,*z).coeffs()+sp.Poly(sp.expand(sum(bhat))-sbb*z2,*z).coeffs()+[sp.expand(sa_*sbb-9*c),sp.expand(inv*k*c-1)]
    build('s22o%d'%o,ahat,bhat,list(v)+list(w)+[k,c,sa_,sb_,sbb,inv],extra)
