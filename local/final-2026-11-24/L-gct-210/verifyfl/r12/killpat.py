import sys, os, re, signal
"""killpat.py -- kill every process whose command line matches REGEX, EXCEPT this process, its ancestors (my own shell) and any process whose
   command line mentions killpat.py.  Prints what it killed.  usage: python3 -I killpat.py REGEX [--dry]"""
pat = re.compile(sys.argv[1]); dry = '--dry' in sys.argv
me = os.getpid(); anc = set()
q = me
while q > 1:
    anc.add(q)
    try:
        with open('/proc/%d/stat' % q) as f: q = int(f.read().rsplit(')', 1)[1].split()[1])
    except Exception: break
for d in os.listdir('/proc'):
    if not d.isdigit() or int(d) in anc: continue
    try:
        cmd = open('/proc/%s/cmdline' % d, 'rb').read().replace(b'\0', b' ').decode(errors='replace')
    except Exception: continue
    if 'killpat.py' in cmd or not pat.search(cmd): continue
    print(('would kill' if dry else 'kill'), d, cmd[:110])
    if not dry:
        try: os.kill(int(d), signal.SIGKILL)
        except Exception as e: print('  failed', e)
