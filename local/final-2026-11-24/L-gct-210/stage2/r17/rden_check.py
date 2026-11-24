# Check: the lcm of the rref denominators of each tree family is a product of that family's exceptional factors (so T1cert excluded nothing extra).
import json, subprocess, sympy as sp, sys
st=json.load(open('/home/kevxhk/work/L-gct-210/stage2/r16/tree_R2.json'))
code="""import sys
sys.argv=['x','R2','0',%r]
src=open('/home/kevxhk/work/L-gct-210/stage2/r16_F2col_setup.py').read()
exec(src.split("    print('rref done")[0].replace("if os.path.exists(_ck):","if False:"))
d=sp.Integer(1)
for e in R:
    if e!=0: d=sp.lcm(d,sp.fraction(sp.together(e))[1])
print('RDEN',sp.factor(d))"""
for k,r in st.items():
    o=subprocess.run(['python3','-I','-c',code%r['fix']],capture_output=True,text=True).stdout
    rd=[l for l in o.splitlines() if l.startswith('RDEN')]
    print(repr(r['fix']).ljust(30),rd[0] if rd else o[-200:],' | exc',r.get('exceptional'),flush=True)
