# Round 24 (dlt0d): dim Delta = 0 with the FUNCTION-OF-h REDUCTION [rigorous, sec. 44 (D)]: X = {lam (x) h} (+) C x*, s(h) = 1, e2(h) = e3(h) = 0,
# U' = W_h = span(u1 = h^2 - h, u2 = h^2 - h^3) (2-dim: chart u * minor_{01}(u1,u2) = 1, WLOG by S_5). The e^1-coefficient of D_2(x) in U' gives for
# delta_k = r_k - r_0 (k = 1,2): (2h_j - 1) delta_kj = S_k h_j + h_j (h_j - 1)(al_k + B_k h_j), S_k = s(delta_k); gauge r_i -> r_i + nu_i h (sum nu = 0)
# shifts al_k by 2(nu_k - nu_0): al_1 = al_2 = 0. c(x*) = r_0 + r_1 + r_2 in U': c_j = h_j (h_j - 1)(AC + BC h_j). So r_0 = (c - delta_1 - delta_2)/3.
# Chart: one of S1,B1,S2,B2,AC,BC equal to 1 (x* up to scale; all zero => x* = 0). Remaining: level of X, D2 and D3 in U' (3x3 minors with u1,u2).
import sys, itertools; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r16'); from pr3lib import level, deletion
CH,P=sys.argv[1],sys.argv[2]; SCH=sys.argv[3] if len(sys.argv)>3 else 's1'; KH=int(sys.argv[4]) if len(sys.argv)>4 else 0
# s0 variant: s(h) = 0, e1 = e2 = e3 = 0, U' = span(h^2, h^3), chart h_KH = 1; the D2-cut reads 2 h_j delta_kj = S_k h_j + h_j^2 (al_k + B_k h_j), al_k = 0 by gauge.
h=['h%d'%j for j in range(5)]
if SCH=='s0': h[KH]='1'
if SCH=='s1':
    u1=['((%s)^2-(%s))'%(h[j],h[j]) for j in range(5)]; u2=['((%s)^2-(%s)^3)'%(h[j],h[j]) for j in range(5)]
else:
    u1=['((%s)^2)'%h[j] for j in range(5)]; u2=['((%s)^3)'%h[j] for j in range(5)]
par={'S1':'S1','B1':'B1','S2':'S2','B2':'B2','AC':'AC','BC':'BC'}; par[CH]='1'
d1=['d1_%d'%j for j in range(5)]; d2=['d2_%d'%j for j in range(5)]
c=['((%s)*((%s)-%s)*((%s)+(%s)*(%s)))'%(h[j],h[j],'1' if SCH=='s1' else '0',par['AC'],par['BC'],h[j]) for j in range(5)]
r0=['((%s)-(%s)-(%s))/3'%(c[j],d1[j],d2[j]) for j in range(5)]
r1=['(%s+%s)'%(r0[j],d1[j]) for j in range(5)]; r2=['(%s+%s)'%(r0[j],d2[j]) for j in range(5)]
co=['a','b','(-a-b)']; R=[r0,r1,r2]
rows=[['(%s)*%s+e*%s'%(co[i],h[j],R[i][j]) for j in range(5)] for i in range(3)]
lev=level(rows); cc,D2,D3=deletion(rows)
e2='+'.join('%s*%s'%(h[i],h[j]) for i,j in itertools.combinations(range(5),2)); e3='+'.join('%s*%s*%s'%(h[i],h[j],h[k]) for i,j,k in itertools.combinations(range(5),3))
deq=[]
for k,(dk,S,B) in enumerate(((d1,par['S1'],par['B1']),(d2,par['S2'],par['B2']))):
    if SCH=='s1': deq+=['(2*%s-1)*%s-(%s)*%s-%s*(%s-1)*(%s)*%s'%(h[j],dk[j],S,h[j],h[j],h[j],B,h[j]) for j in range(5)]
    else: deq+=['2*%s*%s-(%s)*%s-(%s)^2*(%s)*%s'%(h[j],dk[j],S,h[j],h[j],B,h[j]) for j in range(5)]
    deq.append('(%s)-(%s)'%(S,'+'.join(dk)))
vs=[x for x in h if x!='1']+d1+d2+[p for p in ('S1','B1','S2','B2','AC','BC') if par[p]!='1']+['u']
o=['ring R0=0,(%s,a,b,e),dp;'%','.join(vs),'ideal L=%s;'%','.join(lev),'ideal C=%s,%s,%s-%s,%s; int kk; int ll; matrix M; poly gg;'%(e2,e3,'+'.join(h),'1' if SCH=='s1' else '0',','.join(deq)),
   'for(kk=1;kk<=ncols(L);kk++){ M=coef(L[kk],a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; } }']
for nm,vec in (('D2',D2),('D3',D3)):
    for j in range(5): o.append('poly %s_%d=%s;'%(nm,j,vec[j]))
    for k in (2,3,4):
        o.append('gg=det(matrix(ideal(%s,%s,%s_0, %s,%s,%s_1, %s,%s,%s_%d),3,3)); M=coef(gg,a*b*e); for(ll=1;ll<=ncols(M);ll++){ C=C,M[2,ll]; }'%(u1[0],u2[0],nm,u1[1],u2[1],nm,u1[k],u2[k],nm,k))
o.append('C=C,u*((%s)*(%s)-(%s)*(%s))-1;'%(u1[0],u2[1],u1[1],u2[0]))
o.append('ring R=%s,(%s),dp; ideal C=imap(R0,C); C=simplify(C,2); ideal G=%s(C); "DLT0D %s K%d chart %s: dim",dim(std(G)),"unit",(G[1]==1);'%(P,','.join(vs),'slimgb' if P=='0' else 'std',SCH,KH,CH))
o.append('quit;')
f='/home/kevxhk/work/L-gct-210/stage3/r24/dlt0d_%s%d_%s_%s.sing'%(SCH,KH,CH,'q' if P=='0' else 'p'); open(f,'w').write('\n'.join(o)+'\n'); print(f)
