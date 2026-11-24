import sys, numpy as np, itertools
src = open('/home/kevxhk/work/L-gct-210/stage2/t6_typeII_full.py').read().split("if __name__=='__main__':")[0]
exec(src)
lab = {'C': 0, 'Q': 1, 'B': 2}
def run(cols, tag):
    s12c = tuple(lab[c[0]] for c in cols); s13c = tuple(lab[c[1]] for c in cols); s23c = tuple(lab[c[2]] for c in cols)
    for e12 in (1, -1):
        for e13 in (1, -1):
            w2 = typeII(s12c, e12)[0]; w3 = typeII(s13c, e13)[0]
            for s23 in opts23(w3 / w2):
                if s23[0] != s23c: continue
                res = test((s12c, e12), (s13c, e13), s23)
                if res == 'rankN<5': print(tag, e12, e13, s23, res); continue
                viol, info = res
                print(tag, 'eps', e12, e13, s23[1], 'viol', viol, [x for x in info if x[2] == 'B1'])
T0, T1, T2, T3 = ('C','C','C'), ('C','Q','Q'), ('Q','C','B'), ('B','B','C')
U1, U2, U3 = ('C','B','B'), ('Q','Q','C'), ('B','C','Q')
run([T1, T2, T3, T1, T2], 'O1 F1 (2,2,1)')
run([T1, T2, T3, T3, T3], 'O1 F1 (1,1,3)')
run([U1, U2, U3, U1, U2], 'O2 F1 (2,2,1)')
run([T0, U2, U3, T0, U1], 'O2 F2 a')
run([T0, U2, U3, U1, U1], 'O2 F2 b')
run([T0, U2, U3, U1, U2], 'O2 F2 c')
