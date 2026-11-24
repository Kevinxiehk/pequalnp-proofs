# parse msolve elimination outputs: keep the generators free of the eliminated block; print minimal associated primes (Singular, same char)
import sys, re, glob, subprocess
def elim_part(fn):
    txt=open(fn).read(); hdr=[l for l in txt.split('\n') if l.startswith('#variable order')][0]
    names=[v.strip() for v in hdr.split(':')[1].split(',')]
    nel=int(open(fn.replace('.out','.nelim')).read())
    body=txt[txt.find('['):txt.rfind(']')+1].strip('[]')
    polys=[p.strip() for p in body.replace('\n','').split(',') if p.strip()]
    keep=[p for p in polys if not any(re.search(r'\b%s\^'%v,p) for v in names[:nel])]
    return keep,names[nel:],int(re.search(r'characteristic:\s*(\d+)',txt).group(1))
def minass(polys,names,char):
    if not polys: return ['(0)']
    if polys==['1'] or polys==['1*1'] : return ['UNIT']
    s='LIB "primdec.lib";\nring R=%d,(%s),dp;\nideal J=%s;\nlist L=minAssGTZ(J);\nint i; for(i=1;i<=size(L);i++){print("COMP");print(L[i]);}\nquit;\n'%(char,','.join(names),','.join(polys))
    open('/tmp/minass_tmp.sing','w').write(s)
    r=subprocess.run(['/usr/bin/Singular','-q'],stdin=open('/tmp/minass_tmp.sing'),capture_output=True,text=True,timeout=300)
    comps=[' '.join(c.split()) for c in r.stdout.split('COMP')[1:]]
    return comps if comps else ['UNIT? '+r.stdout[:200]]
if __name__=='__main__':
    for fn in sorted(glob.glob(sys.argv[1])):
        keep,names,char=elim_part(fn)
        if len(keep)==1 and keep[0].replace('1*','')=='1': print(fn.split('/')[-1],': UNIT'); continue
        print(fn.split('/')[-1],':',' | '.join(minass(keep,names,char)))
