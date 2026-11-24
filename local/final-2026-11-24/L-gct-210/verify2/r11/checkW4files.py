# parse Wm from stage3's alpha0_W4n_*.sing and check: columns sum 0, isotropic, special (p3 = 0), all 4 taus = 0, perm = 0; compare Y formula lines
import re, sympy as sp, itertools
I=sp.I
for tag in ('0145','0235','1234'):
    txt=open('/home/kevxhk/work/L-gct-210/stage3/r13/alpha0_W4n_%s.sing'%tag).read()
    W=sp.zeros(4,4)
    for r,j,e in re.findall(r'Wm\[(\d),(\d)\]=(.*?);',txt): W[int(r)-1,int(j)-1]=sp.sympify(e.replace('I','I'),locals={'I':I})
    cols=[W[:,j] for j in range(4)]
    s0=[sp.expand(sum(W[:,j]))==0 for j in range(4)]
    print(tag,'W=',W.tolist())
    print('   col sums zero:',s0,' row sums (sum_j z_j = 0):',[sp.expand(sum(W[r,:]))==0 for r in range(4)])
    print('   isotropic:',[sp.expand((c.T*c)[0])==0 for c in cols],' p3=0:',[sp.expand(sum(x**3 for x in c))==0 for c in cols])
    print('   taus zero:',[sp.expand(sum(W[r,a]*W[r,b]*W[r,c] for r in range(4)))==0 for a,b,c in itertools.combinations(range(4),3)],
          ' perm:',sp.expand(sum(sp.prod([W[r,p[r]] for r in range(4)]) for p in itertools.permutations(range(4)))))
    ylines=[l for l in txt.split('\n') if l.startswith('Y[')]
    print('   Y lines:',len(ylines),'| sample:',ylines[0][:110])
    print('   coef line:',[l for l in txt.split('\n') if 'coef(' in l][0][:120])
