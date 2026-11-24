# compiled_map.py: for every theorem of the full candidate R9f.lean, where (if anywhere) the identical declaration text
# has been compiled with a full proof and no error in its line range.
import re, sys
Z = '/home/kevxhk/work/L-gct-210/lean/zbf/'
LG = '/home/kevxhk/work/L-gct-210/leanzbf/'
def chunks(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    out = []; cur = []; start = 1
    for idx, ln in enumerate(lines, 1):
        if ln and not ln[0].isspace() and cur:
            out.append((start, idx - 1, cur)); cur = []; start = idx
        cur.append(ln)
    out.append((start, len(lines), cur))
    res = {}
    for s, e, ch in out:
        m = re.match(r'theorem (\S+)', ch[0])
        if not m:
            continue
        txt = '\n'.join(ch).rstrip()
        full = not re.search(r':= by\s*\n\s*sorry\s*$', txt)
        res[m.group(1)] = (s, e, txt, full)
    return res
def errlines(log):
    ls = set()
    for line in open(log, encoding='utf-8', errors='replace'):
        m = re.match(r'\S*check\.lean:(\d+):\d+: error', line)
        if m:
            ls.add(int(m.group(1)))
    return ls
def compiled(path, log):
    ch = chunks(path); el = errlines(log); ok = {}
    for n, (s, e, txt, full) in ch.items():
        if full and not any(s <= x <= e for x in el):
            ok[n] = txt
    return ok
import os
TARGET = os.environ.get('TARGET', 'R9f.lean')
R9f = chunks(Z + TARGET)
srcs = {}
srcs['R7s_t3 (w2)'] = compiled(Z + 'R7s_t3.lean', LG + 'R7s_t3_w0036.log')
srcs['R9d (w3)'] = compiled(Z + 'R9d.lean', LG + 'R9d_w0313.log')
r3e = chunks(Z + 'R3e.lean')
srcs['R3e (round 3 full file)'] = {n: v[2] for n, v in r3e.items() if v[3]}
# R6t_stub: current file was modified after window 2 only in r6_3 / r6_4 (gen_t1d.py); count its other full decls
r6 = chunks(Z + 'R6t_stub.lean')
changed = set(re.findall(r'^theorem (\S+)', open(Z + 'r6_3.txt').read() + open(Z + 'r6_4.txt').read(), re.M))
srcs['R6t_stub (w2)'] = {n: v[2] for n, v in r6.items() if v[3] and n not in changed and n != 't1_IIi'}
if len(sys.argv) > 1:
    srcs['R12s_combo (w3)'] = compiled(Z + 'R12s_combo.lean', sys.argv[1])
norm = lambda s: re.sub(r'\s+', ' ', s)
rows = []
for n, (s, e, txt, full) in R9f.items():
    where = [k for k, d in srcs.items() if n in d and norm(d[n]) == norm(txt)]
    rows.append((n, where))
comp = [r for r in rows if r[1]]; notc = [r for r in rows if not r[1]]
print('R9f theorems', len(rows), 'compiled in full somewhere', len(comp), 'not yet', len(notc))
from collections import Counter
print(Counter(w[0] for n, w in comp))
open(LG + 'compiled_map.txt', 'w').write('\n'.join('%s\t%s' % (n, ', '.join(w) if w else 'NOT YET (stub only)') for n, w in rows))
print('not yet:', [n for n, w in notc][:200])
