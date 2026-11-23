import sys; sys.path.insert(0,'.')
import numpy as np, itertools
from core import u, ub, chi, E_of
from hessN import hess, maxiso
one=np.array([1,1,1,0,0.])
gens={('o',a):np.outer(one,chi(a)) for a in range(1,5)}
gens.update({('p',b):np.outer(u,chi(b)) for b in range(5)}); gens.update({('q',c):np.outer(ub,chi(c)) for c in range(5)})
reps=[(('o',1),('p',1),('p',4),('q',2)),(('o',1),('p',4),('q',2),('q',3)),(('p',1),('p',4),('q',2),('q',3))]
import graded3  # recompute list of 18
