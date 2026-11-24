import sys,re
# usage: locate.py LIST LOGFILE   (LIST = space separated part names in build order, w.tail appended automatically)
D='/home/kevxhk/work/L-gct-210/lean/fl'
parts=sys.argv[1].split()+['__tail']
off=[];n=0
for p in parts:
    f=f'{D}/w.tail' if p=='__tail' else f'{D}/{p}.part'
    k=len(open(f).read().split('\n'))-1
    off.append((n+1,n+k,p)); n+=k
for l in open(sys.argv[2]):
    m=re.search(r':(\d+):(\d+): (error|warning)',l)
    if m and m.group(3)=='error':
        ln=int(m.group(1))
        for a,b,p in off:
            if a<=ln<=b:
                print(f'{p}.part:{ln-a+1}: '+l.strip()[:200]); break
    elif 'error' in l.lower() and not m:
        print('  '+l.strip()[:200])
