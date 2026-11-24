# Given a msolve -P 1 parametrization (mod p) of the 0-dim pair scheme in a chart, decide at which points the defect has dim <= 3:
# rank of the 12 generating vectors (d2(u_k, v_l), the 4 cubic coefficients of d3a on W_a, of d3b on W_b) in V5 ~ C^4.
# A random 4x4 combination determinant Det(lambda) in F_p[lambda]/(f): gcd(Det, f) = 1  =>  rank 4 (e = 4) at EVERY point (rigorous over F_p-bar).
# usage: python3 -I evrank.py RURFILE P PIVA PIVB      (PIVA, PIVB like 01 23 = Gr(2,5) chart pivots)
import sys, re, random, itertools, ast
from sympy import Poly, GF, symbols, gcd as sgcd
fn=sys.argv[1]; P=int(sys.argv[2]); pa=[int(c) for c in sys.argv[3]]; pb=[int(c) for c in sys.argv[4]]
txt=open(fn).read().strip().rstrip(':')
data=ast.literal_eval(txt.replace('\n',''))
print('top-level structure:', type(data), len(data) if hasattr(data,'__len__') else '')
print(str(data)[:500])
