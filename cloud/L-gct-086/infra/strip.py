import sys,re
def strip(src):
    out=[];i=0;n=len(src);depth=0
    while i<n:
        if src.startswith('/-',i):
            depth+=1;i+=2;continue
        if depth>0:
            if src.startswith('-/',i): depth-=1;i+=2
            else: i+=1
            continue
        if src.startswith('--',i):
            j=src.find('\n',i); i = n if j<0 else j; continue
        out.append(src[i]);i+=1
    s=''.join(out)
    lines=[l.rstrip() for l in s.split('\n') if not l.startswith('import ')]
    s='\n'.join(lines)
    s=re.sub(r'\n{3,}','\n\n',s)
    return s.strip('\n')+'\n'
print(''.join(strip(open(f,encoding='utf-8').read())+'\n' for f in sys.argv[1:]),end='')
