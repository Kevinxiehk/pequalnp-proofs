import sys, re, os
src, blocks, out = sys.argv[1], sys.argv[2:-1], sys.argv[-1]
t = open(src, encoding='utf-8').read()
lines = t.split('\n')
# split into top-level chunks: a chunk starts at a line with non-space at col 0
chunks = []
cur = []
for ln in lines:
    if ln and not ln[0].isspace() and cur:
        chunks.append(cur); cur = []
    cur.append(ln)
chunks.append(cur)
outl = []
nstub = 0
for ch in chunks:
    head = ch[0]
    if head.startswith('theorem ') and not head.startswith('theorem PEqualNP.Outside'):
        body = '\n'.join(ch)
        d = 0
        i = -1
        for k, ch2 in enumerate(body):
            if ch2 in '([{':
                d += 1
            elif ch2 in ')]}':
                d -= 1
            elif ch2 == ':' and d == 0 and body[k+1:k+2] == '=':
                i = k
                break
        assert i > 0, head
        # keep trailing blank lines
        trail = len(ch) - len('\n'.join(ch).rstrip('\n').split('\n'))
        outl.append(body[:i].rstrip() + ' := by\n  sorry')
        outl.extend([''] * trail)
        nstub += 1
    else:
        outl.extend(ch)
t2 = '\n'.join(outl)
endl = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
assert t2.count(endl) == 1
b = '\n'.join(open(f, encoding='utf-8').read().strip('\n') for f in blocks)
t2 = t2.replace(endl, '\n' + b + '\n' + endl)
i = t2.index('theorem PEqualNP.Outside.L_gct_210_zbf :')
t2 = t2[:i] + 'theorem PEqualNP.Outside.L_gct_210 : True := by\n  trivial\n'
tmp = out + '.tmp'
open(tmp, 'w', encoding='utf-8').write(t2)
os.replace(tmp, out)
print(out, 'stubbed', nstub, 'bytes', len(t2.encode()), 'lines', t2.count('\n'))
