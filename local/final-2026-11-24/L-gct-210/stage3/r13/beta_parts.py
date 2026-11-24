# Round 13: which part of the (beta) conditions is already contradictory?  LM in (t, lambda), l_0 = 1, all l_j != 0 (Rabinowitsch),
# moments M (3 eqs) plus PART in {D3, D4, ALL}.  usage: python3 -I beta_parts.py PART SEED NSTARTS
import sys, itertools, numpy as np
part,seed,NS=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]); rg=np.random.default_rng(seed)
def esym(xs,k): return sum(np.prod(c) for c in itertools.combinations(xs,k)) if k else 1.0
def g(ta,tb,tc): xs=[ta,tb,tc]; return esym(xs,1)+4*esym(xs,2)*esym(xs,3)
def h(ts):
    ts2=[x*x for x in ts]; f=1+16*esym(ts,4)+16*esym(ts,4)**2+4*esym(ts2,2)-8*sum(ts2[m]*esym(ts[:m]+ts[m+1:],2) for m in range(4))
    a,b,c,d=ts; pair=(a-b)**2*(c-d)**2+(a-c)**2*(b-d)**2+(a-d)**2*(b-c)**2; return 8*pair-3*f
def F(x):
    t=x[:5]; l=np.concatenate([[1],x[5:9]]); rr=x[9]
    out=[l.sum(),(l*t).sum(),(l*t*t).sum()]
    if part in ('D3','ALL'):
        R=[l[j]*sum(l[a]*l[b]*g(t[j],t[a],t[b]) for a,b in itertools.combinations([k for k in range(5) if k!=j],2)) for j in range(5)]
        out+=[R[1]-R[0],R[2]-R[0],R[3]-R[0],R[4]+4*R[0]]
    if part in ('D4','ALL'):
        P=[np.prod([l[k] for k in range(5) if k!=j])*h([t[k] for k in range(5) if k!=j]) for j in range(5)]
        out+=[P[1]-P[0],P[2]-P[0],P[3]-P[0],P[4]+4*P[0]]
    out.append(rr*np.prod(l[1:])-1); return np.array(out)
def J(x,hh=1e-7):
    f0=F(x); Jm=np.empty((len(f0),len(x)),complex)
    for i in range(len(x)):
        d=np.zeros(len(x),complex); d[i]=hh; Jm[:,i]=(F(x+d)-f0)/hh
    return f0,Jm
def lm(x,it=300):
    lam=1e-3; f,Jm=J(x); nf=np.linalg.norm(f)
    for _ in range(it):
        A=Jm.conj().T@Jm; gg=Jm.conj().T@f; ok=False
        for _ in range(10):
            d=np.linalg.solve(A+lam*np.eye(len(x)),gg); n2=np.linalg.norm(F(x-d))
            if n2<nf: x=x-d; lam=max(lam/4,1e-15); ok=True; break
            lam*=4
        if not ok: break
        f,Jm=J(x); nf=np.linalg.norm(f)
        if nf<1e-13: break
    return x,nf
hits=0; fl=[]
for st in range(NS):
    x,nf=lm((rg.normal(size=10)+1j*rg.normal(size=10))*0.8); fl.append(nf)
    if nf<1e-10:
        hits+=1; t=x[:5]; l=np.concatenate([[1],x[5:9]])
        if hits<=3: print('hit: t',np.round(t,4),' |l|',np.round(np.abs(l),4),' distinct t:',len(set(np.round(t,6))),flush=True)
print('PART %s: %d hits in %d starts, residual quantiles %s'%(part,hits,NS,np.round(np.quantile(fl,[0,.25,.5]),8)),flush=True)
