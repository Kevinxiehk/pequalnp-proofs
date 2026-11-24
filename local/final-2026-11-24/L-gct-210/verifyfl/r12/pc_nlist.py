import sys, os, subprocess; sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/exact'); sys.path.insert(0, '/home/kevxhk/work/L-gct-210/verifyfl/r12')
"""pc_nlist.py -- rerun given N-system files (written by pc_nsweep.py) under the RSS cap with a longer timeout.
   usage: python3 -I pc_nlist.py CAP_MB TMO file.ms [...]"""
cap, tmo = sys.argv[1], sys.argv[2]
for fn in sys.argv[3:]:
    if os.path.exists(fn + '.gb'): os.remove(fn + '.gb')
    rr = subprocess.run(['python3', '-I', '/home/kevxhk/work/L-gct-210/verifyfl/r12/rsscap.py', cap, tmo, '/usr/bin/msolve', '-g', '2', '-t', '1', '-f', fn, '-o', fn + '.gb'], capture_output=True, text=True)
    if rr.returncode != 0 or not os.path.exists(fn + '.gb') or os.path.getsize(fn + '.gb') == 0:
        v = 'FAIL(%s)' % (rr.stdout.strip() if 'RSSCAP' in rr.stdout else 'rc%d' % rr.returncode)
    else:
        b = open(fn + '.gb').read(); b = b[b.index('['):].strip().rstrip(':').strip()[1:-1]; v = 'UNIT' if b.strip() == '1' else 'NONUNIT(%d)' % len([x for x in b.split(',\n') if x.strip()])
    print('%s: %s' % (os.path.basename(fn), v), flush=True)
