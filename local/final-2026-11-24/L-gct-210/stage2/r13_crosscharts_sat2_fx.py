# Parametric FO2-joint chart test for the cross-type family (a1,a2,a3 free; chart a4 = 1), forms from r13_crossforms.py times D.
# For every chart of Gr(4,8): msolve (char CH) on the isotropy equations of L'' for P_2*D and B_z*D (z = z^(1..3)). Prints non-unit charts.
import sys, itertools, subprocess, os, re, sympy as sp
exec(open('/home/kevxhk/work/L-gct-210/stage2/r15_msstr_fixed.py').read())

CH=sys.argv[1]; TH=sys.argv[2] if len(sys.argv)>2 else '1'
src=open('/home/kevxhk/work/L-gct-210/stage2/r13_crossforms.py').read().split("print('P_2 =',q0)")[0]
exec(src)
coords=[sig,s4,ph4,u1,u2,u3,u4,t04]
forms=[sp.expand(sp.cancel(q0*D))]+[sp.expand(sp.cancel(b*D)) for b in Bz]
def gram(f):
    return sp.Matrix(8,8,lambda i,j: sp.diff(f,coords[i],coords[j])/(1 if i!=j else 2) if True else 0)
Gs=[gram(f) for f in forms]
ys=[[sp.Symbol('y%d_%d'%(r,c)) for c in range(4)] for r in range(4)]; flat=[v for row in ys for v in row]
wd='/tmp/st2_cross_%d'%os.getpid(); os.makedirs(wd,exist_ok=True); bad=0; n=0; failed=0
for S in [tuple(int(c) for c in x.split('-')) for x in os.environ.get('CHARTS','').split()] or itertools.combinations(range(8),4):
    rest=[c for c in range(8) if c not in S]; Lm=sp.zeros(4,8)
    for r in range(4):
        Lm[r,S[r]]=1
        for bi,c in enumerate(rest): Lm[r,c]=ys[r][bi]
    polys=[]
    for G in Gs:
        P=(Lm*G*Lm.T).applyfunc(sp.expand)
        for i in range(4):
            for j in range(i,4):
                if P[i,j]!=0: polys.append(P[i,j])
    fn=wd+'/c.ms'; out=wd+'/c.out'
    if os.path.exists(out): os.remove(out)
    wv=sp.Symbol('wD'); polys.append(sp.expand(wv*D*(a1+a2+a3+1)-1))
    open(fn,'w').write(','.join(str(v) for v in flat+[a1,a2,a3,wv])+'\n'+CH+'\n'+',\n'.join(msstr(e,flat+[a1,a2,a3,wv],CH) for e in polys)+'\n')
    subprocess.run('ulimit -v '+os.environ.get('MSV','2000000')+'; msolve -g 2 -t %s -f %s -o %s > /dev/null 2>&1'%(TH,fn,out),shell=True)
    fresh=os.path.exists(out) and os.path.getmtime(out)>=os.path.getmtime(fn)
    res=open(out).read() if fresh else 'NOOUT'
    body=''.join(l for l in res.splitlines() if not l.startswith('#')); unit=re.sub(r'\s','',body)=='[1]:'
    n+=1
    if res=='NOOUT' or body.strip()=='':
        failed+=1; print('FAILED chart',S,flush=True); continue
    if not unit:
        bad+=1; print('NONUNIT chart',S,flush=True)
        # elimination of the chart variables: which a's?
        print('   GB head:',body[:300],flush=True)
    elif n%10==0: print('  charts done',n,flush=True)
print('polynomials with rational coefficients (now cleared):',NONINT[0],flush=True); print('RESULT cross family charts char %s: %d charts, non-unit %d, FAILED %d'%(CH,n,bad,failed),flush=True)
