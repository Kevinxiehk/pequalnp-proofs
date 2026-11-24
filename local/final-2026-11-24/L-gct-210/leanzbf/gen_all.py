# gen_all.py K N: run gen_cfg.py on killed configurations number K*N .. K*N+N-1 (sorted), log status and size.
import sys, ast, glob, subprocess, time
K, N = int(sys.argv[1]), int(sys.argv[2])
surv = set()
for f in glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_dump_p*.log'):
    for line in open(f):
        if 'survivor' in line:
            t = ast.literal_eval(line.split('survivor', 1)[1].strip())
            surv.add((t[0], t[1], t[2]))
cfgs = set()
for f in glob.glob('/home/kevxhk/work/L-gct-210/leanzbf/r3_export_p*.txt'):
    for line in open(f):
        if line.strip():
            r = ast.literal_eval(line)
            cfgs.add((r['s12'], r['s13'], r['eps']))
killed = sorted(c for c in cfgs if c not in surv)
print('killed', len(killed), 'survivors', len(surv), flush=True)
for c in killed[K * N:(K + 1) * N]:
    a = ''.join(map(str, c[0])); b = ''.join(map(str, c[1])); e = str(c[2])
    out = '/home/kevxhk/work/L-gct-210/leanzbf/cfg_out/%s_%s_%s.txt' % (a, b, 'p' if c[2] == 1 else 'm')
    t0 = time.time()
    try:
        p = subprocess.run(['python3', '-I', '/home/kevxhk/work/L-gct-210/leanzbf/gen_cfg.py', a, b, e, out],
                           capture_output=True, text=True, timeout=300)
        st = 'ok' if p.returncode == 0 else 'FAIL ' + (p.stderr.strip().splitlines() or ['?'])[-1][:120]
        msg = p.stdout.strip().splitlines()
    except subprocess.TimeoutExpired:
        st = 'TIMEOUT'; msg = []
    print(a, b, e, st, ' | '.join(msg[-2:]), '%.0fs' % (time.time() - t0), flush=True)
