import numpy as np
exec(open('p3full.py').read().split("rows=[]")[0])
mx=0
for _ in range(20):
    t=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)); t-=t.mean()
    r=t.sum(1); c=t.sum(0); ph=t-(r[:,None]+c[None,:])/2
    e2=(ph**2).sum()-2*Pk2(t)-1.25*((r**2).sum()+(c**2).sum())
    e3=(ph**3).sum()-1.5*Pk3(t)+0.375*((r**3).sum()+(c**3).sum())
    mx=max(mx,abs(e2),abs(e3))
print('max identity error',mx)
