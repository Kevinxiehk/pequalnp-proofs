import random
def rnd(): return complex(random.uniform(-1,1), random.uniform(-1,1))
t=[rnd() for _ in range(5)]; I=[rnd() for _ in range(5)]; sy=[rnd() for _ in range(5)]; ss=rnd()
m=[rnd() for _ in range(5)]; kap=rnd(); th=rnd()
T=sum(t); Q=sum(x*x for x in t); W=sum(I); M=sum(m); M2=sum(x*x for x in m)
def closed(b): return (T-t[b])**2-(Q-t[b]**2)-ss+2*sy[b]-2*I[b]+W
R=[closed(b)-th*m[b] for b in range(5)]
hT=T; hsum=sum(sy)-ss; ht=[t[b]-kap*m[b] for b in range(5)]; hm=M
ha=W-ss-kap**2*M2
certa=(1/3)*sum(R)+(th/3)*hm-T*hT-(2/3)*hsum+sum((t[b]+kap*m[b])*ht[b] for b in range(5))
print(abs(ha-certa))
for j in range(5):
    goal=I[j]-sy[j]-kap**2*m[j]**2+(th/2)*m[j]
    cert=(-1/2)*R[j]+(1/2)*(T-2*t[j])*hT+(t[j]+kap*m[j])*ht[j]-(1/2)*sum((t[b]+kap*m[b])*ht[b] for b in range(5))+(1/2)*ha
    print(abs(goal-cert))
# T certificate
b0=3
L1=[m[b0]*6*(T-t[b])-m[b]*6*(T-t[b0]) for b in range(5)]
print(abs(m[b0]*T-((1/24)*sum(L1)+(1/4)*(T-t[b0])*hm)))
hk=kap*m[b0]-t[b0]
b=1
print(abs((m[b0]*t[b]-m[b0]*kap*m[b])-((m[b0]-m[b])*hT-(1/6)*L1[b]-m[b]*hk)))
