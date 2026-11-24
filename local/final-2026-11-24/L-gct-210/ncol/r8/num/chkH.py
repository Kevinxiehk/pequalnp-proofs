# re-check a lmH solution on FRESH random points (the LM residual uses only 18 sample points: possible under-sampling)
import numpy as np, sys
typ=sys.argv[1]; f=sys.argv[2]
src=open('lmH.py').read()
src=src.split('best=[]')[0].replace("typ=sys.argv[1]; seed=int(sys.argv[2]); nst=int(sys.argv[3]); DK=int(sys.argv[4]) if len(sys.argv)>4 else 4","typ='%s'; seed=12345; nst=0; DK=int(sys.argv[3]) if len(sys.argv)>3 else 4"%typ).replace('NS=18','NS=60')
exec(src)
x=np.load(f); r=resid(x); print(f,'residual on 60 fresh points: %.3e'%(r@r))
