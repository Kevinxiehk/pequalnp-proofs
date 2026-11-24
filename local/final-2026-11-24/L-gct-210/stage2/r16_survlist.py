# Turn the kernel-kill tree state (r16/tree_<RUL>.json) into survivor jobs for r16/surv_run.sh [NOTES-stage2 R16]:
#   q0(k,k) hyperplane f = 0 in a family  ->  "K2 <cache> <var>=<solution>"   (kernel-reduced charts, Gr(3,nq-2))
#   rank-drop component (Groebner basis, zero-dimensional in the a's)  ->  "V4 <RUL> <family fix + point>"   (full Gr(4,8), remaining params free)
# Points/lines lying on a setup-exceptional factor of the family are skipped (covered by the child family).
import sys, json, sympy as sp
RUL=sys.argv[1]; st=json.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/tree_%s.json'%RUL))
nu,a1,a2,a3,lam=sp.symbols('nu a1 a2 a3 lam'); loc={'nu':nu,'a1':a1,'a2':a2,'a3':a3,'lam':lam}
jobs=[]; manual=[]
for key,rec in st.items():
    v=rec.get('verdict',''); fx=rec.get('fix','')
    fixd={k:sp.sympify(x,locals=loc) for k,x in (kv.split('=') for kv in fx.split(',') if kv)}
    if not v.startswith('survivors') and not v.startswith('JUMP-TYPE'): manual.append((fx,v)); continue
    exc=[sp.sympify(x,locals=loc) for x in sp.sympify(rec.get('exceptional','[]'),locals=loc)]
    hyp=sp.sympify(v.split('survivors')[1].split(';')[0].strip().lstrip(':').strip(),locals=loc)
    for f in hyp:
        f=sp.sympify(f); fv=sorted(f.free_symbols,key=str)
        x=[s for s in [a1,a2,a3,nu,lam] if s in fv and sp.Poly(f,s).degree()==1 and sp.Poly(f,s).coeff_monomial(s).is_number][0]
        sol=sp.solve(f,x)[0]
        if v.startswith('JUMP-TYPE'): jobs.append('K2 %s %s=%s   # JUMP-TYPE family %s: needs its Deg too'%(rec['cache'],x,sp.sstr(sol).replace(' ',''),fx))
        else: jobs.append('K2 %s %s=%s'%(rec['cache'],x,sp.sstr(sol).replace(' ','')))
    if 'rank-drop:' in v:
        for comp in v.split('rank-drop:')[1].split('|'):
            comp=comp.strip()
            if not comp: continue
            G=sp.sympify(comp,locals=loc); free=sorted(set().union(*[g.free_symbols for g in G]),key=str)
            for s in sp.solve(G,free,dict=True):
                if any(sp.simplify(e.subs(s))==0 for e in exc if e.free_symbols and e.free_symbols<=set(s.keys())|set()): continue
                if any(not sp.sympify(val).is_number for val in s.values()): manual.append((fx,'non-point rank-drop component %s'%comp)); continue
                full=dict((str(k),val) for k,val in fixd.items()); full.update({str(k):val for k,val in s.items()})
                full={k:sp.simplify(sp.sympify(val).subs({sp.Symbol(kk):vv for kk,vv in full.items() if kk!=k})) for k,val in full.items()}
                jobs.append('V4 %s %s'%(RUL,','.join('%s=%s'%(k,sp.sstr(val).replace(' ','')) for k,val in sorted(full.items()))))
seen=set()
for j in jobs:
    if j not in seen: seen.add(j); print(j)
for m in manual: print('# MANUAL',m[0],':',m[1][:200])
