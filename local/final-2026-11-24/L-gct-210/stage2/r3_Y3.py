# Round 3: sanity test of LEMMA Y3 (factorisation for 2-row elements with exactly three nonzero columns) on the exact examples.
# y in L supported on rows a,b and columns Sig (|Sig| = 3), {d,e} = Sig^c, i a third row, {i',i''} the other two rows.
# On V0 := {u in L^ : u_id = u_ie = 0}:  perm(u with rows a,b replaced by y_a,y_b) = q_de(u_i',u_i'') * <Q*,u_i> = 0, hence
#   (i) <Q*,u_i> = 0 on V0   or   (ii) q_de(u_i',u_i'') = 0 on V0  [then dim{u in L^ : u[ii'i'';de] = 0} >= dim V0 - 2].
import sys, itertools, numpy as np
sys.path.insert(0,'/home/kevxhk/work/L-gct-210/chief'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage2')
from core import SP, perm
from pairlib import nullspace, rank
rng=np.random.default_rng(3)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
tot=0; viol=0; stats={}
for name,f in SP.items():
    B=f(); n=len(B); Bh=np.concatenate([np.ones((1,5,5),complex),B])
    for a,b in itertools.combinations(range(5),2):
        oth=[i for i in range(5) if i not in (a,b)]
        # 2-row elements on rows a,b
        A=np.array([[B[k][i,j] for k in range(n)] for i in oth for j in range(5)])
        N=nullspace(A)
        if N.shape[1]==0: continue
        Y=np.tensordot(N.T,B,1)                      # basis of Y_ab
        # candidate elements: basis vectors and random combos; keep those with exactly 3 nonzero columns
        cands=[Y[k] for k in range(len(Y))]+[np.tensordot(rnd(len(Y)),Y,1) for _ in range(3)]
        # also try to zero out columns: elements of Y_ab vanishing on a column pair
        for d,e in itertools.combinations(range(5),2):
            M=np.array([[Y[k][i,j] for k in range(len(Y))] for i in (a,b) for j in (d,e)]); NN=nullspace(M)
            for q in range(NN.shape[1]): cands.append(np.tensordot(NN[:,q],Y,1))
            if NN.shape[1]>=2:
                for _ in range(2): cands.append(np.tensordot(NN@rnd(NN.shape[1]),Y,1))
        seen=[]
        for y in cands:
            sup=[j for j in range(5) if np.abs(y[:,j]).max()>1e-9]
            if len(sup)!=3: continue
            if any(rank(np.array([y.reshape(-1),s.reshape(-1)]))==1 for s in seen): continue
            seen.append(y)
            d,e=[j for j in range(5) if j not in sup]
            Q={T:y[a,T[0]]*y[b,T[1]]+y[a,T[1]]*y[b,T[0]] for T in itertools.combinations(sup,2)}
            if max(abs(v) for v in Q.values())<1e-9: continue
            Qs=np.zeros(5,complex)
            for p in sup:
                T=tuple(j for j in sup if j!=p); Qs[p]=Q[T]
            for i in oth:
                i1,i2=[r for r in oth if r!=i]
                C=np.array([[Bh[k][i,d] for k in range(n+1)],[Bh[k][i,e] for k in range(n+1)]]); V0=nullspace(C)
                lin=[];quad=[];ident=0
                for _ in range(6):
                    c=V0@rnd(V0.shape[1]); u=np.tensordot(c,Bh,1)
                    um=u.copy(); um[a]=y[a]; um[b]=y[b]
                    l=Qs@u[i]; q=u[i1,d]*u[i2,e]+u[i1,e]*u[i2,d]
                    ident=max(ident,abs(perm(um)),abs(perm(um)-q*l)); lin.append(abs(l)); quad.append(abs(q))
                tot+=1
                case='(i)' if max(lin)<1e-8 else ('(ii)' if max(quad)<1e-8 else 'NEITHER')
                ok= ident<1e-7 and case!='NEITHER'
                if case=='(ii)':
                    K=np.array([[Bh[k][r,c] for k in range(n+1)] for r in oth for c in (d,e)]); dk=nullspace(K).shape[1]
                    ok = ok and dk>=V0.shape[1]-2
                viol+= (not ok); stats[(name,case)]=stats.get((name,case),0)+1
print('Lemma Y3 on the examples: cases',tot,' violations',viol); print(stats)
