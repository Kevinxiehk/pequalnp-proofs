import numpy as np, sys, glob, io, contextlib
sys.path.insert(0,'.'); sys.path.insert(0,'../methods')
from core import *; from c35 import *
import spaces
def load(f):
    a=np.load(f); return a.reshape(len(a),25)
S={}
for f in sorted(glob.glob('../lowd/p23gen_7_*.npy'))+['../lowd/p23supp_7_23_142_1.npy','../lowd/p23supp_7_23_142_2.npy']: S[f.split('/')[-1]]=load(f)
for k in ['ex1','ex2','L080','rank1weight']: S[k]=spaces.SP[k]()
S['rc45p1']=load('../split/rc45p1.npy'); S['weight6']=load('../dc5/weight6_p23.npy'); S['k4gen']=load('../dc5/k4gen.npy')
S['d5sol']=load('../dc5/sol_d5_k23_s1.npy')
for k,B in S.items():
    B=B-B.mean(1,keepdims=True); Lu=orth(Phi(B)); analyse(Lu,k)
rng=np.random.default_rng(3)
for l in [5,7,9]:
    analyse(rand_iso(l,rng),'randiso%d'%l)
