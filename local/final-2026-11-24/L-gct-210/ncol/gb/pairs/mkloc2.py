# local multiplicities (Singular ds) of I and of I + det(M) at the same-node points of chart 01_01 / 01_02, mod p (same M as mksing.py, same seed)
import sys, itertools, subprocess
P=int(sys.argv[1]); chart=sys.argv[2]; seed=sys.argv[3]
pa,pb=chart.split('_')
subprocess.run(['python3','-I','mksing.py',str(P),pa,pb,seed,'sing/tmp_%s.sing'%chart],check=True)
base=open('sing/tmp_%s.sing'%chart).read().split('\n')
head=[l for l in base if l.startswith('ring') or l.startswith('option') or l.startswith('ideal I') or l.startswith('matrix M') or l.startswith('M[')]
I_=next(c for a in range(2,10**6) for c in [pow(a,(P-1)//4,P)] if c*c%P==P-1)
roots={'i':I_,'-1':P-1,'-i':P-I_}
pts=[]
for perm in itertools.permutations(['i','-1','-i']):
    v=[roots[x] for x in perm]
    if chart=='01_01':
        pts.append(('n0_'+'_'.join(perm),[0,0,0]+v+[0,0,0]+v))
        pts.append(('n1_'+'_'.join(perm),v+[0,0,0]+v+[0,0,0]))
    else:
        c=[0,1]+v; inv=pow(c[2],P-2,P); w=[x*inv%P for x in c]
        pts.append(('n0_'+'_'.join(perm),[0,0,0]+v+[0,0,0]+[w[1],w[3],w[4]]))
for name,pt in pts:
    L=list(head)+['poly D = det(M);','ring Rl = %d, (t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11), ds;'%P,
       'map f = Rg, %s;'%(','.join('t%d+(%d)'%(k,pt[k]) for k in range(12))),
       'ideal Il = f(I); poly Dl = f(D);','"LOC %s Y", vdim(std(Il));'%name,'"LOC %s Y+D", vdim(std(Il+ideal(Dl)));'%name,'quit;']
    open('sing/loc_%s_%s.sing'%(chart,name),'w').write('\n'.join(L)+'\n')
print(len(pts),'scripts')
