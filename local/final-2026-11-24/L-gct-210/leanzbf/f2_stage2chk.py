import sys, numpy as np, itertools
src = open('/home/kevxhk/work/L-gct-210/stage2/t6_typeII_full.py').read().split("if __name__=='__main__':")[0]
exec(src)
lab = {'C': 0, 'Q': 1, 'B': 2}
cols = [('C','C','C'), ('Q','C','B'), ('B','B','C'), ('C','C','C'), ('C','Q','Q')]
s12c = tuple(lab[c[0]] for c in cols); s13c = tuple(lab[c[1]] for c in cols); s23c = tuple(lab[c[2]] for c in cols)
for e12 in (1, -1):
    for e13 in (1, -1):
        w2 = typeII(s12c, e12)[0]; w3 = typeII(s13c, e13)[0]
        for s23 in opts23(w3 / w2):
            if s23[0] != s23c: continue
            res = test((s12c, e12), (s13c, e13), s23)
            if res == 'rankN<5': print(e12, e13, s23, res); continue
            viol, info = res
            print('eps', e12, e13, s23[1], 'viol', viol)
            for x in info: print('   ', x)
