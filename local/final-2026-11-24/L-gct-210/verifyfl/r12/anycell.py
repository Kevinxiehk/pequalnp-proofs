import sys, os, importlib; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r7'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
# VOID (round 13, R13.5): the radical equations here use columns 3, 4 of Y_rad = 0, which is wrong (b_n(Y) = 2 y_n - s(Y)); use radcell.py / gen_t22rad.
"""anycell.py (generalises sc0rad.py) -- one S-cell of a rho = 2 [T22] piece built by GENMODULE.build(p, *ARGS, scell, keyed=True), optionally
   (S-cell 0 only, RCHART r1/r2; RCHART - = none) with the RADICAL equations (round 13, NOTES R13.1).
   (F4) refined [rigorous, char p > 3]: for an active neutral column n (image C v_n on N), b_n(K) c v_n^perp and b_n^* g = s^* g, so
   g|S = phi^* gbar with phi: S -> v_n^perp / C v_n (1-dim, gbar nondegenerate); S is not totally isotropic, hence rank phi = 1 and the
   radical C r of S is ker phi: every Y with s(Y) = r has b_n(Y) in C v_n.  With the gauge (entry (vrow_n, n) of the D-part = 0, and
   v_n[vrow_n] = 1) the radical element Y_rad = rho_1 Y_1 + rho_2 Y_2 has b_n(Y_rad) = 0, for n = 3 AND n = 4 (rho = 2).
   Equations added: <s_rad, s_1> = <s_rad, s_2> = 0 (s_rad = rho_1 s_1 + rho_2 s_2 spans the radical), col 3 and col 4 of Y_rad = 0.
   Radical charts: 'r1' (rho_1 = 1, rho_2 free) and 'r2' (rho_1 = 0, rho_2 = 1); both together cover.
   Stages N+Y_1 | N+Y_2 | all (subcut_fixed.run) with GB_N inherited from N_GB_FILE if given (msolve output of the piece's N-system).
   usage: python3 -I anycell.py P GENMODULE "ARGS" SCELL RCHART OUTPREFIX TMO [N_GB_FILE]
          ARGS = the generator's build arguments before scell, e.g. "A,0,01" for gen_t22t0c.build(p, 'A', 0, '01', 0, keyed=True)"""
import subcut_fixed as subcut; sys.modules['subcut'] = subcut
import exactlib as X, gen_n3
p, gm, args, sc, rch, out, tmo = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5], sys.argv[6], float(sys.argv[7])
assert rch == '-' or sc == 0
G = importlib.import_module(gm)
av = [int(a) if a.isdigit() else a for a in args.split(',')]
nm, eqs, extra = G.build(p, *av, sc, keyed=True)
nm = list(nm); extra = list(extra); ix = {n: i for i, n in enumerate(nm)}
var = lambda n: {(ix[n],): 1}
if rch != '-':
    # rebuild Y_1, Y_2 exactly as the generators do (gen_n3.svectors scell 0 + dc_matrix of w_r)
    b = [[1, p - 1, 0, 0], [0, 1, p - 1, 0], [0, 0, 1, p - 1]]
    S = [[X.padd(X.pconst(b[0][a], p), X.pmul(var('sal'), X.pconst(b[2][a], p), p), p) for a in range(4)],
         [X.padd(X.pconst(b[1][a], p), X.pmul(var('sbe'), X.pconst(b[2][a], p), p), p) for a in range(4)]]
    Y = [X.dc_matrix([var('w%d_%d' % (r, d)) for d in range(12)], p) for r in range(2)]
    if rch == 'r1':
        k = len(nm); nm.append('rho2'); rho = [X.pconst(1, p), {(k,): 1}]
    else: rho = [{}, X.pconst(1, p)]
    srad = [X.padd(X.pmul(rho[0], S[0][a], p), X.pmul(rho[1], S[1][a], p), p) for a in range(4)]
    extra += [gen_n3.ip(srad, S[0], p), gen_n3.ip(srad, S[1], p)]
    for n in (3, 4):
        for a in range(4):
            q = X.padd(X.pmul(rho[0], Y[0][a][n], p), X.pmul(rho[1], Y[1][a][n], p), p)
            if q: extra.append(q)
extra = [e for e in extra if e]
pre = []
if len(sys.argv) > 8 and os.path.exists(sys.argv[8]) and '[' in open(sys.argv[8]).read():      # an empty/crashed N-GB file is ignored
    s = open(sys.argv[8]).read(); body = s[s.index('['):].strip().rstrip(':').strip()[1:-1]; pre = [x.strip() for x in body.split(',\n') if x.strip()]
try:
    v = subcut.run(nm, eqs, extra, p, [[0, 1, 2], [0, 1, 3], [0, 1, 2, 3]], out, tmo, pre=pre)
except Exception as exn:
    v = 'FAIL(%s)' % type(exn).__name__
print('VERDICT anycell %s %s scell %d %s: %s' % (gm, args, sc, rch, v), flush=True)
