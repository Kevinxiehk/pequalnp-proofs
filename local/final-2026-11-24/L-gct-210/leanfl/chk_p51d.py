import sympy as sp
ph=sp.symbols('ph0:4'); w=sp.symbols('w0:4'); fs=sp.symbols('fs0:4'); lam,c=sp.symbols('lam c')
ip=lambda u,v: sum(u[i]*v[i] for i in range(4))
e3=ip(ph,ph)-ip(w,w)
hu=[ph[i]-lam*w[i]-c*fs[i] for i in range(4)]
hlam2=lam**2-1; hss=ip(fs,fs)
goal=2*lam*c*ip(w,fs)
comb=e3-sum((ph[i]+lam*w[i]+c*fs[i])*hu[i] for i in range(4))-ip(w,w)*hlam2-c**2*hss
print('hc0', sp.expand(goal-comb))
