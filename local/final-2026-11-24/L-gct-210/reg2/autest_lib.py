# side-effect-free copies of AU / inside from autest.py
import numpy as np
from t import null, rank
def AU(U):
    A=np.concatenate([U,np.ones((1,5))],0); ann=null(A)
    conds=[a*w for a in ann for w in U]
    if not conds: return np.eye(5,dtype=complex)
    return null(np.array(conds))
def inside(V,W,tol=1e-6):
    if len(V)==0: return True
    return rank(np.concatenate([W,V],0),tol)==rank(W,tol)
