import sys, os
# usage: stub2.py SRC STUBBED_BLOCKS... -- FULL_BLOCKS... OUT ; every theorem of SRC and of the STUBBED blocks gets proof sorry
args = sys.argv[1:]
src, out = args[0], args[-1]
k = args.index('--')
sblocks, fblocks = args[1:k], args[k + 1:-1]
def stub_text(t, keep_final=False):
    lines = t.split('\n'); chunks = []; cur = []
    for ln in lines:
        if ln and not ln[0].isspace() and cur:
            chunks.append(cur); cur = []
        cur.append(ln)
    chunks.append(cur)
    outl = []; n = 0
    for ch in chunks:
        head = ch[0]
        if head.startswith('theorem ') and not head.startswith('theorem PEqualNP.Outside'):
            body = '\n'.join(ch); d = 0; i = -1
            for j, c in enumerate(body):
                if c in '([{': d += 1
                elif c in ')]}': d -= 1
                elif c == ':' and d == 0 and body[j + 1:j + 2] == '=':
                    i = j; break
            assert i > 0, head
            trail = len(ch) - len(body.rstrip('\n').split('\n'))
            outl.append(body[:i].rstrip() + ' := by\n  sorry'); outl.extend([''] * trail); n += 1
        else:
            outl.extend(ch)
    return '\n'.join(outl), n
t2, n0 = stub_text(open(src, encoding='utf-8').read())
sb = []; n1 = 0
for f in sblocks:
    s, n = stub_text(open(f, encoding='utf-8').read().strip('\n')); sb.append(s); n1 += n
fb = [open(f, encoding='utf-8').read().strip('\n') for f in fblocks]
endl = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
assert t2.count(endl) == 1
t2 = t2.replace(endl, '\n' + '\n\n'.join(sb + fb) + '\n' + endl)
i = t2.index('theorem PEqualNP.Outside.L_gct_210_zbf :')
t2 = t2[:i] + 'theorem PEqualNP.Outside.L_gct_210 : True := by\n  trivial\n'
tmp = out + '.tmp'
open(tmp, 'w', encoding='utf-8').write(t2); os.replace(tmp, out)
print(out, 'stubbed', n0, '+', n1, 'bytes', len(t2.encode()), 'lines', t2.count('\n'))
