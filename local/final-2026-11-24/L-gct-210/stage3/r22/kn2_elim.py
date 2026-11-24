import sys,re,subprocess
r,k,XC=sys.argv[1:4]
f=subprocess.run(['python3','-I','/home/kevxhk/work/L-gct-210/stage3/r22/kn2_fam.py',r,k,XC,'t'],capture_output=True,text=True).stdout.strip()
s=open(f).read(); vs=re.search(r'ring R=\(0,w\),\(([^)]*)\)',s).group(1).split(',')
pr='*'.join(x for x in vs if x!='t')
s=re.sub(r'"kn2fam pair.*\n','"dim",dim(G); ideal E=eliminate(G,%s); "t-projection:"; E;\n'%pr,s)
g=f.replace('.sing','_el.sing'); open(g,'w').write(s); print(g)
