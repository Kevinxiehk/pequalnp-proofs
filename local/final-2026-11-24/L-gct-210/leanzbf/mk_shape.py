# mk_shape.py BASE OUT KEEP_BLOCKS... -- EXTRA_BLOCKS... : stub every theorem of BASE except those defined in KEEP_BLOCKS,
# then append EXTRA_BLOCKS (full) before the namespace end.
import sys, re, os
args = sys.argv[1:]
base, out = args[0], args[1]
k = args.index('--')
keep_blocks, extra = args[2:k], args[k + 1:]
keep = set()
for f in keep_blocks:
    for m in re.finditer(r'^(?:theorem|lemma) (\S+)', open(f, encoding='utf-8').read(), re.M):
        keep.add(m.group(1))
t = open(base, encoding='utf-8').read()
lines = t.split('\n'); chunks = []; cur = []
for ln in lines:
    if ln and not ln[0].isspace() and cur:
        chunks.append(cur); cur = []
    cur.append(ln)
chunks.append(cur)
outl = []; ns = nk = 0
pending_opt = None
for ch in chunks:
    head = ch[0]
    m = re.match(r'theorem (\S+)', head)
    if m and not head.startswith('theorem PEqualNP.Outside') and m.group(1) not in keep:
        body = '\n'.join(ch); d = 0; i = -1
        for j, c in enumerate(body):
            if c in '([{': d += 1
            elif c in ')]}': d -= 1
            elif c == ':' and d == 0 and body[j + 1:j + 2] == '=':
                i = j; break
        assert i > 0, head
        outl.append(body[:i].rstrip() + ' := by\n  sorry'); outl.append(''); ns += 1
    else:
        if m:
            nk += 1
        outl.extend(ch)
t2 = '\n'.join(outl)
endl = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
assert t2.count(endl) == 1
eb = [open(f, encoding='utf-8').read().strip('\n') for f in extra]
t2 = t2.replace(endl, '\n' + '\n\n'.join(eb) + '\n' + endl)
t2 = re.sub(r'\n{3,}', '\n\n', t2)
open(out + '.tmp', 'w', encoding='utf-8').write(t2); os.replace(out + '.tmp', out)
print(out, 'stubbed', ns, 'kept', nk, 'lines', t2.count('\n'), 'bytes', len(t2.encode()))
