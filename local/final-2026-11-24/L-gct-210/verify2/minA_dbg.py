import random, itertools
src=open('/home/kevxhk/work/L-gct-210/verify2/minA_rank.py').read().split("e1=[1,0]")[0]
exec(src)
random.seed(1)
# consume the same random stream as the 0-triangle test is not needed; just search
cnt={}
ex=None
for _ in range(400):
    p={}
    for i in range(3):
        while True:
            u=[random.randint(-5,5),random.randint(-5,5)]; v=[random.randint(-5,5),random.randint(-5,5)]
            if u[0]*v[1]-u[1]*v[0]!=0: break
        o=[k for k in range(3) if k!=i]
        p[i]={o[0]:u,o[1]:[random.choice([1,2,-3])*x for x in u],3:v}
    while True:
        vs=[[random.randint(-5,5),random.randint(-5,5)] for _ in range(3)]
        if all(vs[x][0]*vs[y][1]-vs[x][1]*vs[y][0]!=0 for x in range(3) for y in range(x+1,3)): break
    p[3]={k:v for k,v in zip((0,1,2),vs)}
    r=span_rank(p); cnt[r]=cnt.get(r,0)+1
    if r==15 and ex is None: ex=p
print(cnt); print(ex)
