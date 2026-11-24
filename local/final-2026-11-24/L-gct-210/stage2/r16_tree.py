# Recursive kernel-kill tree for an F2col ruling [NOTES-stage2 R16]. A family = a set of LINEAR constraints on (nu, a1, a2, a3) (chart a4 = 1).
# For each family: setup (r16_F2col_setup.py, exact T_1 on the family) + kernel analysis (r16_Kauto.py). Children = the families cut out by each
# linear setup-exceptional factor (forms' denominators, complement determinant, T_1 rank-jump gcd). Families are deduplicated by the reduced row
# echelon form of their constraints. Output per family: survivors (q0(k,k) hyperplanes -> K2 runs; rank-drop components -> V4 runs) or MANUAL.
# usage: r16_tree.py RUL MAXDEPTH ['root1|root2|...'], a root = constraints separated by ';' (e.g. 'nu|a1|nu+1')     (state in r16/tree_<RUL>.json, resumable)
import sys, os, re, json, subprocess, sympy as sp
RUL=sys.argv[1]; MAXD=int(sys.argv[2]); roots=[[c for c in r.split(';') if c] for r in (sys.argv[3].split('|') if len(sys.argv)>3 else [''])]
nu,a1,a2,a3,lam=sp.symbols('nu a1 a2 a3 lam'); V=[lam if RUL=='R1' else nu,a1,a2,a3]; loc={str(v):v for v in V}
ST='/home/kevxhk/work/L-gct-210/stage2/r16/tree_%s.json'%RUL
state=json.load(open(ST)) if os.path.exists(ST) else {}
def canon(cons):
    if not cons: return ()
    M=sp.Matrix([[sp.Poly(c,*V).coeff_monomial(v) for v in V]+[sp.Poly(c,*V).coeff_monomial(1)] for c in cons])
    Rr,_=M.rref(); rows=[tuple(str(x) for x in Rr.row(i)) for i in range(Rr.rows) if any(x!=0 for x in Rr.row(i))]
    return tuple(rows)
def fixstr(cons):
    if not cons: return ''
    sol=sp.solve(cons,[v for v in [V[1],V[0],V[2],V[3]]],dict=True)[0]
    return ','.join('%s=%s'%(k,sp.sstr(sp.expand(v)).replace(' ','')) for k,v in sol.items())
def linear(f): return sp.Poly(f,*V).total_degree()==1
queue=[([sp.sympify(c,locals=loc) for c in r],1 if r else 0) for r in roots]; seen=set()
while queue:
    cons,d=queue.pop(0); key=str(canon(cons))
    if key in seen: continue
    seen.add(key)
    if any(len(set(canon(cons)))>4 for _ in [0]): continue
    try: fs=fixstr(cons)
    except Exception as ex: print('UNSOLVABLE',cons,ex,flush=True); continue
    if key in state: rec=state[key]; print('[cached]',RUL,fs,'->',rec['verdict'],flush=True)
    else:
        print('######## family',RUL,repr(fs),'depth',d,flush=True)
        o=subprocess.run(['timeout','2400','python3','-I','/home/kevxhk/work/L-gct-210/stage2/r16_F2col_setup.py',RUL,'2147483629',fs],capture_output=True,text=True).stdout
        m=re.search(r'(/home\S*cache_[0-9a-f]+\.pkl)',o)
        if not m: rec={'fix':fs,'verdict':'SETUP FAILED','log':o[-500:]}
        else:
            a=subprocess.run(['timeout','2400','python3','-I','/home/kevxhk/work/L-gct-210/stage2/r16_Kauto.py',m.group(1)],capture_output=True,text=True).stdout
            info={l.split(':')[0].strip():l for l in o.splitlines() if re.match(r'(rank-jump|dim T_1|complement valid|denominators)',l)}
            rec={'fix':fs,'cache':m.group(1),'setup':[l for l in o.splitlines() if re.match(r'(rank-jump|dim T_1|complement valid|denominators)',l)],'kauto':a}
            if 'NOT the standard case' in a: rec['verdict']='MANUAL (non-standard rank structure)'
            elif 'FIXED MEMBER' in a: rec['verdict']=[l for l in a.splitlines() if 'FIXED MEMBER' in l][0]
            elif 'JUMP-TYPE KILL' in a:
                rec['verdict']='JUMP-TYPE: survivors '+a.split('factors (non-exceptional):')[1].split(' U ')[0].strip()+' ; plus Deg (to compute)'
            elif 'SURVIVORS' in a:
                sv=[l for l in a.splitlines() if l.startswith('SURVIVORS')][0]; rd=a.split('Groebner components:')[1].split('SURVIVORS')[0].strip().splitlines()
                rec['verdict']='survivors: '+sv.split('factors (non-exceptional):')[1].split(' U ')[0].strip()+' ; rank-drop: '+' | '.join(x.strip() for x in rd)
            else: rec['verdict']='ERROR: '+a[-300:]
            ex=[l for l in a.splitlines() if l.startswith('setup-exceptional factors:')]
            rec['exceptional']=ex[0].split(':',1)[1].strip() if ex else '[]'
        state[key]=rec; json.dump(state,open(ST,'w'),indent=1)
        print('   setup:',rec.get('setup'),flush=True); print('   verdict:',rec['verdict'],flush=True); print('   exceptional:',rec.get('exceptional'),flush=True)
    if d<MAXD and 'exceptional' in rec:
        for f in sp.sympify(rec['exceptional'],locals=loc):
            f=sp.sympify(f)
            if f.free_symbols and linear(f): queue.append((cons+[f],d+1))
            elif f.free_symbols: print('   NONLINEAR exceptional factor (manual):',f,flush=True)
print('TREE DONE',flush=True)
