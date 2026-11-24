# find linear_combination certificates: goal (lhs-rhs) = sum coef_i * (h_i lhs - rhs), coef_i polynomials over Q from a monomial set
import sympy as sp, itertools
def monos(vars_, deg):
    out = [sp.Integer(1)]
    for d in range(1, deg + 1):
        for comb in itertools.combinations_with_replacement(vars_, d):
            out.append(sp.Mul(*comb))
    return out
def find_lc(goal, hyps, vars_, deg):
    names = list(hyps)
    ms = monos(vars_, deg)
    unk = []
    expr = sp.expand(goal)
    coefs = {}
    for n in names:
        cs = sp.symbols(f'k_{n}_0:{len(ms)}')
        unk += cs
        coefs[n] = sum(ci * mi for ci, mi in zip(cs, ms))
        expr -= sp.expand(coefs[n] * hyps[n])
    expr = sp.expand(expr)
    eqs = sp.Poly(expr, *vars_).coeffs()
    sol = sp.solve(eqs, unk, dict=True)
    if not sol: return None
    s = sol[0]
    res = {}
    for n in names:
        cexpr = sp.expand(coefs[n].subs(s).subs({u: 0 for u in unk}))
        if cexpr != 0: res[n] = cexpr
    # verify
    chk = sp.expand(goal - sum(res[n] * hyps[n] for n in res))
    assert chk == 0, chk
    return res
