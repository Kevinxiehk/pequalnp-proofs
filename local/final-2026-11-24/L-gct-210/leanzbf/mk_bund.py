# mk_bund.py BASE OUT BLOCKS... : like mk_e5test.py (stub every theorem of BASE, insert BLOCKS before the namespace end),
# but drops from BASE every theorem/def whose name is (re)defined in BLOCKS.
import sys, re, os
base, out = sys.argv[1], sys.argv[2]
blocks = sys.argv[3:]
mid = '\n\n'.join(open(f, encoding='utf-8').read().strip('\n') for f in blocks)
newnames = set(re.findall(r'^(?:theorem|def|noncomputable def) (\S+)', mid, flags=re.M))
t = open(base, encoding='utf-8').read()
endm = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
i1 = t.index(endm) + 1
pre, post = t[:i1], t[i1:]
lines = pre.split('\n'); chunks = []; cur = []
for ln in lines:
    if ln and not ln[0].isspace() and cur:
        chunks.append(cur); cur = []
    cur.append(ln)
chunks.append(cur)
outl = []; n = 0; dropped = 0; pend = []
for ch in chunks:
    head = ch[0]
    if head.startswith('set_option maxHeartbeats') and head.endswith(' in'):
        pend = ch; continue
    m = re.match(r'(?:theorem|def|noncomputable def) (\S+)', head)
    if m and m.group(1) in newnames:
        dropped += 1; pend = []; continue
    outl.extend(pend); pend = []
    if head.startswith('theorem ') and not head.startswith('theorem PEqualNP.Outside'):
        body = '\n'.join(ch); d = 0; i = -1
        for j, c in enumerate(body):
            if c in '([{': d += 1
            elif c in ')]}': d -= 1
            elif c == ':' and d == 0 and body[j + 1:j + 2] == '=':
                i = j; break
        assert i > 0, head
        outl.append(body[:i].rstrip() + ' := by\n  sorry'); outl.append(''); n += 1
    else:
        outl.extend(ch)
t2 = '\n'.join(outl).rstrip('\n') + '\n\n' + mid + '\n\n' + post
t2 = re.sub(r'\n{3,}', '\n\n', t2)
open(out + '.tmp', 'w', encoding='utf-8').write(t2); os.replace(out + '.tmp', out)
print(out, 'stubbed', n, 'dropped', dropped, 'lines', t2.count('\n'), 'bytes', len(t2.encode()))
