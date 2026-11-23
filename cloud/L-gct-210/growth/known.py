import numpy as np, sys, glob
sys.path.insert(0,'.'); sys.path.insert(0,'../methods')
from core import *
import spaces
def load(f):
    a=np.load(f); return a.reshape(len(a),25)
S={}
for f in sorted(glob.glob('../lowd/p23*_7_*.npy'))+sorted(glob.glob('../lowd/p23*_8_*.npy')): S[f.split('/')[-1]]=load(f)
for k in ['ex1','ex2','L080','rank1weight']: S[k]=spaces.SP[k]()
S['rc45p1']=load('../split/rc45p1.npy'); S['weight6']=load('../dc5/weight6_p23.npy'); S['k4gen']=load('../dc5/k4gen.npy')
S['gr1111']=load('../dc5/gr_012_1111.npy'); S['d6sol']=load('../dc5/sol_d6_k23_s1.npy'); S['d5sol']=load('../dc5/sol_d5_k23_s1.npy')
for k,B in S.items():
    B=B-B.mean(1,keepdims=True)
    Lu=orth(Phi(B))
    q,t=checkP23(Lu)
    l,pp,g=growth(Lu,1e-7)
    print('%-28s dim %d  |Q| %.1e |T| %.1e  dim L∘L %2d  dim(L+L∘L) %2d  24-l %d  slack %d'%(k,l,q,t,pp,g,24-l,24-l-g))
