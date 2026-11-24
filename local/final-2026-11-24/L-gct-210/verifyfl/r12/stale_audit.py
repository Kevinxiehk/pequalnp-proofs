import os, sys
"""E-STALE-OUTPUT audit (round 12): for every X.ms.gb next to X.ms under the given roots, a stale read by the LAST call on X.ms
   shows as mtime(X.ms.gb) < mtime(X.ms) (the driver writes X.ms right before each call; msolve truncates X.ms.gb at startup
   whenever it starts at all -- tested: it truncates before any crash at ulimit >= 20 MB; only exec failure / missing input leave it)."""
tot = unit = old = old_unit = empty = 0; bad = []
for root in sys.argv[1:]:
    for d, _, fs in os.walk(root):
        for f in fs:
            if not f.endswith('.ms.gb'): continue
            g = os.path.join(d, f); m = g[:-3]
            if not os.path.exists(m): continue
            tot += 1; s = open(g, errors='replace').read()
            body = ''.join(l for l in s.splitlines() if not l.startswith('#')).replace(' ', '').rstrip(':')
            u = body == '[1]'; unit += u; empty += (os.path.getsize(g) == 0)
            if os.path.getmtime(g) < os.path.getmtime(m) - 1e-6:
                old += 1; old_unit += u; bad.append((u, g))
print('pairs %d  unit-gb %d  empty-gb %d  gb-older-than-ms %d  of which unit %d' % (tot, unit, empty, old, old_unit))
for u, g in sorted(bad, reverse=True)[:40]: print('  %s %s' % ('UNIT' if u else 'other', g))
