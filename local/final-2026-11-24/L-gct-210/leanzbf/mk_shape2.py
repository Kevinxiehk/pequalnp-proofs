# mk_shape2.py BASE OUT FIRST_DECL BLOCKS... : remove from BASE everything from the line 'theorem FIRST_DECL' up to the
# 'set_option ... in / theorem t3_trans' marker, stub all remaining theorems, insert BLOCKS (full) at that position.
import sys, re, os
base, out, first = sys.argv[1], sys.argv[2], sys.argv[3]
blocks = sys.argv[4:]
t = open(base, encoding='utf-8').read()
i0 = t.index('\ntheorem %s ' % first) + 1
i1 = t.index('\nset_option maxHeartbeats 50000000 in\ntheorem t3_trans') + 1
pre, post = t[:i0], t[i1:]
def stub(s):
    lines = s.split('\n'); chunks = []; cur = []
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
            outl.append(body[:i].rstrip() + ' := by\n  sorry'); outl.append(''); n += 1
        else:
            outl.extend(ch)
    return '\n'.join(outl), n
p1, n1 = stub(pre); p2, n2 = stub(post)
mid = '\n\n'.join(open(f, encoding='utf-8').read().strip('\n') for f in blocks)
t2 = p1.rstrip('\n') + '\n\n' + mid + '\n\n' + p2
t2 = re.sub(r'\n{3,}', '\n\n', t2)
open(out + '.tmp', 'w', encoding='utf-8').write(t2); os.replace(out + '.tmp', out)
print(out, 'stubbed', n1 + n2, 'lines', t2.count('\n'), 'bytes', len(t2.encode()))
