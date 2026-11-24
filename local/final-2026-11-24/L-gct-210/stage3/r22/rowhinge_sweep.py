# sweep: case A, |S| = nS, |F| = nF: for every x*-chart (I,J), h-hinge h_j (j in S), and row hinge (row i, minor (a,b), a<b over all columns),
# test the system; UNIT for all row hinges of row i means row i's projection is 1-dim on every solution of that chart. Output summary.
import sys, subprocess, itertools
nS,nF,TO=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3])
base='/home/kevxhk/work/L-gct-210/stage3/r22'
log=open(base+'/rowhinge_%d%d.log'%(nS,nF),'a')
cols=range(5)
for I in (0,1):
    for J in range(5):
        for hj in range(nS):
            res={}
            for i in range(3):
                vals=[]
                for a,b in itertools.combinations(cols,2):
                    f=subprocess.run(['python3','-I',base+'/eqtA.py',str(nS),str(nF),'0','%d%d'%(I,J),'0','h%d+%d%d%d'%(hj,i,a,b)],capture_output=True,text=True).stdout.strip()
                    try:
                        r=subprocess.run(['bash','-c','ulimit -v 500000; Singular -q %s'%f],capture_output=True,text=True,timeout=TO).stdout
                        v='U' if 'unit 1' in r else ('N' if 'unit 0' in r else 'E')
                    except subprocess.TimeoutExpired: v='T'
                    vals.append(v)
                res[i]=''.join(vals)
            log.write('chart %d%d h%d: row0 %s row1 %s row2 %s\n'%(I,J,hj,res[0],res[1],res[2])); log.flush()
