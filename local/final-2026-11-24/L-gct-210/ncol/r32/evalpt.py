# evaluate the polynomials of an msolve file at a point mod p; prints the number of nonvanishing equations
import sys, re
f=sys.argv[1]; P=int(sys.argv[2]); pt=dict(kv.split('=') for kv in sys.argv[3:])
lines=open(f).read().split('\n'); vars_=lines[0].split(','); body=''.join(lines[2:]).replace('^','**')
eqs=[e for e in body.split(',') if e.strip()]
env={v:int(pt.get(v,'0'))%P for v in vars_}
bad=[i for i,e in enumerate(eqs) if eval(e,{},env)%P!=0]
print('%s: %d equations, %d nonvanishing at the point'%(f,len(eqs),len(bad)), bad[:10])
