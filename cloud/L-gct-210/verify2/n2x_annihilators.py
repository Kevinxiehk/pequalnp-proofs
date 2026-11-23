# verify2: exact check of the annihilators K(S2) = {Q in A_2 : Q S2 = 0 in A_4} used in stage3's Theorem N2-X, case (beta).
# A = C[y_0..y_4]/(y_j^2).  S2 = V_3 V_3 (three distinct planes) or P V_3 (P_k = P_l = P).  Random rational data, exact arithmetic.
import itertools, random, importlib.util
from fractions import Fraction as Fr
spec=importlib.util.spec_from_file_location('ex7','/home/claude/work/L-gct-210/rows/exact7.py'); ex7=importlib.util.module_from_spec(spec); spec.loader.exec_module(ex7)
pairs=list(itertools.combinations(range(5),2)); pi={p:k for k,p in enumerate(pairs)}; fours=list(itertools.combinations(range(5),4))
def prod2(y,z): return [y[p]*z[q]+y[q]*z[p] for (p,q) in pairs]          # Y Z in A_2
def cond_rows(S2):
    """rows of linear conditions on Q (10 coords): for each generator s in S2 and each 4-set F: sum_{T in F} Q[T] s[F-T] = 0"""
    rows=[]
    for s in S2:
        for F in fours:
            r=[Fr(0)]*10
            for T in itertools.combinations(F,2):
                Tc=tuple(x for x in F if x not in T); r[pi[T]]+=s[pi[Tc]]
            rows.append(r)
    return rows
def Kdim(S2): return 10-ex7.rank(cond_rows(S2)) if S2 else 10
def inK(Q,S2): return all(sum(a*b for a,b in zip(r,Q))==0 for r in cond_rows(S2))
def VV(V): return [prod2(V[i],V[j]) for i in range(len(V)) for j in range(i,len(V))]
def PV(P,V): return [prod2(p,v) for p in P for v in V]
rnd=random.Random(7); R=lambda: Fr(rnd.choice([-5,-4,-3,-2,-1,1,2,3,4,5]),rnd.choice([1,1,2,3]))
vec=lambda d:[Fr(d.get(j,0)) for j in range(5)]
def lin(*vs):          # random combination
    c=[R() for _ in vs]; return [sum(c[k]*vs[k][j] for k in range(len(vs))) for j in range(5)]
def add(*vs): return [sum(v[j] for v in vs) for j in range(5)]
print('type : case : dim K  (claimed)  [extra membership checks]')
for trial in range(3):
    # (2,3): A={0,1}, B={2,3,4}
    a0,a1,b2,b3,b4=R(),R(),R(),R(),R()
    h=vec({0:a1,1:-a0}); hs=vec({0:a1,1:a0}); u0=vec({2:b3,3:-b2}); u1=vec({3:b4,4:-b3}); V3=[h,u0,u1]
    Qb=[Fr(0)]*10; Qb[pi[(3,4)]]=b2; Qb[pi[(2,4)]]=b3; Qb[pi[(2,3)]]=b4
    g=lin(u0,u1); g2=lin(u0,u1)
    print('(2,3): V3V3:',Kdim(VV(V3)),'(0) | P=V_B:',Kdim(PV([u0,u1],V3)),'(1), Q_beta in K:',inK(Qb,PV([u0,u1],V3)),
          '| P=Cu+C(h+u\'):',Kdim(PV([g,add(h,g2)],V3)),'(0) | P=Cu+Ch:',Kdim(PV([g,h],V3)),'(1)')
    # (2,2): A={0,1}, B={2,3}, free 4
    hp=vec({2:b3,3:-b2}); hps=vec({2:b3,3:b2}); e4=vec({4:1}); V3=[h,hp,e4]; HH=prod2(hs,hps)
    x,xp=R(),R(); P1=[lin(h,hp,e4),lin(h,hp,e4)]; P2=[e4,[x*h[j]+xp*hp[j] for j in range(5)]]; P3=[e4,h]
    print('(2,2): V3V3:',Kdim(VV(V3)),'(1), H*H\'* in K:',inK(HH,VV(V3)),'| e5 not in P:',Kdim(PV(P1,V3)),'(1) | P=Ce5+C(xh+x\'h\'):',Kdim(PV(P2,V3)),'(1) | P=Ce5+Ch:',Kdim(PV(P3,V3)),
          '(2), H*H\'*, H*y5 in K:',inK(HH,PV(P3,V3)),inK(prod2(hs,e4),PV(P3,V3)))
    # (1,3): alpha=e_0, B={1,2,3}, x=4
    c1,c2,c3=R(),R(),R(); v0=vec({1:c2,2:-c1}); v1=vec({2:c3,3:-c2}); V3=[v0,v1,e4]
    Qb=[Fr(0)]*10; Qb[pi[(2,3)]]=c1; Qb[pi[(1,3)]]=c2; Qb[pi[(1,2)]]=c3
    Pgen=[lin(v0,v1,e4),lin(v0,v1,e4)]; uu=lin(v0,v1)
    print('(1,3): V3V3:',Kdim(VV(V3)),'(1), Q_beta in K:',inK(Qb,VV(V3)),'| P=V_B:',Kdim(PV([v0,v1],V3)),'(1) | e_x not in P:',Kdim(PV(Pgen,V3)),'(1) | P=Ce_x+Cu0:',Kdim(PV([e4,uu],V3)),'(2)')
    # (1,4): alpha=e_0, beta zero-free on {1,2,3,4}
    d=[R() for _ in range(4)]; w0=vec({1:d[1],2:-d[0]}); w1=vec({2:d[2],3:-d[1]}); w2=vec({3:d[3],4:-d[2]}); V3=[w0,w1,w2]
    print('(1,4): V3V3:',Kdim(VV(V3)),'(0 inside A_N; total incl. y_0-terms) | P generic:',Kdim(PV([lin(w0,w1,w2),lin(w0,w1,w2)],V3)))
    # (1,2): alpha=e_0, B={1,2}, C={3,4}
    hB=vec({1:c2,2:-c1}); hBs=vec({1:c2,2:c1}); e3=vec({3:1}); V3=[hB,e3,e4]
    print('(1,2): V3V3:',Kdim(VV(V3)),'(2), H_B* y_3, H_B* y_4 in K:',inK(prod2(hBs,e3),VV(V3)),inK(prod2(hBs,e4),VV(V3)),'| P generic:',Kdim(PV([lin(hB,e3,e4),lin(hB,e3,e4)],V3)),
          '| P=Ch_B+Ce_3:',Kdim(PV([hB,e3],V3)),'| P=C^C:',Kdim(PV([e3,e4],V3)))
    # (1,1): alpha=e_0, beta=e_1: V3 = C^{234}
    e2=vec({2:1}); V3=[e2,e3,e4]
    print('(1,1): V3V3:',Kdim(VV(V3)),'(3) | P generic:',Kdim(PV([lin(e2,e3,e4),lin(e2,e3,e4)],V3)),'| P=span(e_2,e_3):',Kdim(PV([e2,e3],V3)))
