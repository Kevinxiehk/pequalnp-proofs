import os, re, sys, collections
root = os.path.expanduser('~/work')
num = re.compile(r'(?<![A-Za-z_0-9^.])(\d+)')
bad = collections.defaultdict(list); tot = collections.Counter(); chars = collections.Counter()
for dp, dn, fn in os.walk(root):
    for f in fn:
        if not f.endswith('.ms'): continue
        path = os.path.join(dp, f)
        try:
            with open(path) as fh:
                fh.readline(); c = fh.readline().strip()
                try: p = int(c)
                except: continue
                chars[p] += 1
                if p == 0: continue
                d = os.path.relpath(dp, root); tot[d] += 1
                mx = 0
                for line in fh:
                    for m in num.findall(line):
                        if len(m) >= 10 or int(m) >= p:
                            v = int(m)
                            if v >= p: mx = max(mx, v)
                if mx: bad[d].append((f, mx))
        except Exception as e:
            print('ERR', path, e, file=sys.stderr)
print('characteristics:', dict(chars))
for d in sorted(tot):
    b = bad.get(d, [])
    print('%-45s modp files %5d   with coeff >= p: %5d %s' % (d, tot[d], len(b), ('e.g. %s max %d' % b[0]) if b else ''))
