# Singular scripts: local multiplicities of J_k (chart 01_01 / 01_02 kernel systems, h-chart k) at the same-node points, char p.
import itertools, sys
P=2147483629
I=next(c for a in range(2,10**6) for c in [pow(a,(P-1)//4,P)] if c*c%P==P-1)
roots={'i':I,'-1':P-1,'-i':P-I}
def pts(chart):
    out=[]
    for perm in itertools.permutations(['i','-1','-i']):
        v=[roots[x] for x in perm]
        if chart=='01_01':
            # node 0: u1 = e0 (t0..t2 = 0), u2 = chi (t3..t5 = v); same for W_b; h-chart 0
            out.append(('n0_'+'_'.join(perm),0,[0,0,0]+v+[0,0,0]+v))
            # node 1: u1 = chi (t0..t2 = v), u2 = e1 (t3..t5 = 0); h-chart 1
            out.append(('n1_'+'_'.join(perm),1,v+[0,0,0]+v+[0,0,0]))
        if chart=='01_02':
            # W_a chart (0,1): node 0, u1 = e0, u2 = chi (chi_1 = 1, t3..t5 = chi_2..chi_4 = v)
            # W_b chart (0,2): v1 = e0 (v1[0]=1,v1[2]=0) -> t6..t8 = entries 1,3,4 of e0 = 0; v2 = chi/chi_2 (v2[0]=0, v2[2]=1) -> entries 1,3,4
            c=[0,1]+v            # chi = (0,1,v2,v3,v4)
            c2=c[2]; inv=pow(c2,P-2,P); w=[x*inv%P for x in c]
            out.append(('n0_'+'_'.join(perm),0,[0,0,0]+v+[0,0,0]+[w[1],w[3],w[4]]))
    return out
chart=sys.argv[1]
for name,hk,pt in pts(chart):
    fn='../ker%s/k_%s_h%d.ms'%('01' if chart=='01_01' else '02',chart,hk)
    L=open(fn).read().split('\n'); vars_=L[0].split(','); polys=''.join(L[2:]).strip().rstrip(',')
    vals=pt+[0,0,0]
    s='ring R0 = %d, (%s), dp;\nideal J = %s;\nring R1 = %d, (%s), ds;\nmap f = R0, %s;\nideal Jl = f(J);\noption(redSB);\nideal G = std(Jl);\n"LOCALMULT %s", vdim(G);\nquit;\n'%(
        P,','.join(vars_),polys,P,','.join(vars_),','.join('%s+(%d)'%(vv,val) for vv,val in zip(vars_,vals)),name)
    open('%s_%s.sing'%(chart,name),'w').write(s)
print('ok')
