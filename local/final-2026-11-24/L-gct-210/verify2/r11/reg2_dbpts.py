exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# BB:")[0])
exec(open('/home/kevxhk/work/L-gct-210/verify2/r11/reg2_r56.py').read().split("# DOUBLE-BLOCK (a,b)")[1].split("\n",1)[1].split("run('DOUBLE")[0])
for (a,b) in [(0,F(1,3)),(0,1),(0,0)]: run('DBLOCK (a,b)=(%s,%s)'%(a,b),dblock(a,b))
