# T1cert (Singular std over QQ, proof grade) for every family of the kernel-kill tree [NOTES-stage2 R17]. Excluded: the family's own exceptional factors,
# plus (nu-1)(3nu+1) when nu is free (those slices are row/swap-symmetry images of nu = 0, 1/3). Non-unit charts -> rerun mod p with ELIM=1.
import json, subprocess, os, re, sympy as sp
st=json.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/tree_R2.json'))
for key,r in st.items():
    fx=r['fix']; exc=r.get('exceptional','[]')
    ex=[str(e) for e in sp.sympify(exc)]
    if 'nu=' not in fx: ex.append('(nu-1)*(3*nu+1)')
    env=dict(os.environ,ENGINE='sing',EXC=','.join(ex))
    print('######## R2',repr(fx),'EXC',ex,flush=True)
    o=subprocess.run(['timeout','1200','python3','-I','/home/kevxhk/work/L-gct-210/stage2/r16_T1cert.py','R2','0',fx],capture_output=True,text=True,env=env).stdout
    print('\n'.join(l for l in o.splitlines() if re.match(r'(NONUNIT|FAILED|RESULT|fixed member)',l)),flush=True)
    if 'non-unit 0' not in o:
        env2=dict(env,ENGINE='',ELIM='1')
        o2=subprocess.run(['timeout','1200','python3','-I','/home/kevxhk/work/L-gct-210/stage2/r16_T1cert.py','R2','2147483629',fx],capture_output=True,text=True,env=env2).stdout
        print('\n'.join('   [mod p] '+l for l in o2.splitlines() if re.match(r'(NONUNIT|   parameter|RESULT)',l)),flush=True)
print('T1CERT TREE DONE',flush=True)
