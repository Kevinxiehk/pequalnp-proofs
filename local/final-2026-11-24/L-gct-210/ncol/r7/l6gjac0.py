# char-0 check of the three lam = 0 points of the general-Z system (L6G): build the system over Q(w) (minpoly w^2+w+1) and compute the
# Jacobian rank at the point (must equal the number of unknowns: local length 1 in characteristic 0).  usage: python3 -I l6gjac0.py UC ZC "c1=..,c2=.."
import sys, subprocess
uc,zc,ptstr=sys.argv[1],sys.argv[2],sys.argv[3]
subprocess.run(['python3','-I','r211G.py','65521',uc,zc,'/tmp/ncol_g0.ms'],check=True)
s=open('/tmp/ncol_g0.sing').read()
lines=s.split('\n')
lines[0]=lines[0].replace('ring R = 65521,','ring R = (0,w),')
lines.insert(1,'minpoly = w^2+w+1;')
s='\n'.join(lines).replace('poly w = ','poly wDUMMY = ').replace('poly i3 = %d;'%pow(3,65519,65521),'number i3 = 1/3;')
cut=s.index('E = simplify(E, 2+4+8);')
unk=lines[0].split('(')[2].split(',k1')[0]   # unknown list from ring line
vals=dict(kv.split('=') for kv in ptstr.split(',') if kv)
mp=','.join(vals.get(v,'0') for v in unk.split(','))
s=s[:cut]+'''E = simplify(E, 2+4+8); "NEQ", size(E);
matrix Jm = jacob(E);
ring Rp = (0,w), (%s), dp; minpoly = w^2+w+1;
map f = R, %s;
matrix Jp = f(Jm); ideal Ep = f(E);
"VANISH", size(simplify(Ep,2))==0;
"JACRANK", rank(Jp), "NVARS", nvars(Rp);
quit;
'''%(unk, mp+','+','.join(['0']*7))
open('/tmp/ncol_g0c.sing','w').write(s)
print(subprocess.run(['Singular','-q','/tmp/ncol_g0c.sing'],capture_output=True,text=True).stdout)
