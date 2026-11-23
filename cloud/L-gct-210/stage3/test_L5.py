import itertools
# (L5) tight case, fixed column j: four triangles D_l (l = the 4 other columns) with G_j = union of the D_l and every edge e of G_j
# lying in exactly 4 - |C_e| + 1 ... precisely label(e) = {l : e not in D_l} must have size 1 or 2 (support size 2 or 3).
V=range(5); TRI=[frozenset(frozenset(p) for p in itertools.combinations(t,2)) for t in itertools.combinations(V,3)]
res={}
for Ds in itertools.product(range(10),repeat=4):
    D=[TRI[i] for i in Ds]; G=set().union(*D)
    lab={e:[l for l in range(4) if e not in D[l]] for e in G}
    if all(len(v) in (1,2) for v in lab.values()):
        n2=sum(1 for v in lab.values() if len(v)==1); n3=sum(1 for v in lab.values() if len(v)==2)
        verts=set().union(*G); deg=sorted(sum(1 for e in G if v in e) for v in verts)
        res.setdefault((n2,n3,len(G),tuple(deg)),0); res[(n2,n3,len(G),tuple(deg))]+=1
for k,v in sorted(res.items()): print('(n2,n3,#edges,degree sequence) =',k,' count',v)
