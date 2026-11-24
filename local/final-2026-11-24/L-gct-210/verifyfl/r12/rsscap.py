import sys, os, time, subprocess
"""rsscap.py -- run a command; kill its whole process group if the summed RSS of the group exceeds CAP_MB (pool rule while the big slot is
   busy: <= 0.5 GB per job).  usage: python3 -I rsscap.py CAP_MB TIMEOUT_S cmd args...   (exit code 137 + message on a cap kill)"""
cap, tmo, cmd = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3:]
p = subprocess.Popen(cmd, start_new_session=True)
pg = os.getpgid(p.pid); t0 = time.time()
def group_rss():
    tot = 0
    for d in os.listdir('/proc'):
        if not d.isdigit(): continue
        try:
            with open('/proc/%s/stat' % d) as f: st = f.read().split()
            if int(st[4]) != pg: continue
            with open('/proc/%s/statm' % d) as f: tot += int(f.read().split()[1]) * os.sysconf('SC_PAGE_SIZE')
        except Exception: pass
    return tot / 1e6
while p.poll() is None:
    time.sleep(2)
    r = group_rss()
    if r > cap or time.time() - t0 > tmo:
        os.killpg(pg, 9); p.wait()
        print('RSSCAP: killed (%s: rss %.0f MB, %.0f s)' % ('rss cap' if r > cap else 'timeout', r, time.time() - t0), flush=True); sys.exit(137)
sys.exit(p.returncode)
