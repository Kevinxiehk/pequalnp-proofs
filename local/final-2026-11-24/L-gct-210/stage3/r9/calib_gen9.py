# calibration of gen9.py: M_0 (y_r = e_0, p = -e_0, w = -(0,-1,-1,3,-1), g_a = -g_b = n, g_c = -g_d = n') must satisfy all LEVEL
# polynomials of case C1G (rab = 0, u = 0, chart iw=0, ia=1, ic=1) mod p (omega in F_p), and must violate FULL ((iii) fails on M_0).
import sys; sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/r9'); sys.path.insert(0,'/home/kevxhk/work/L-gct-210/stage3/gb')
import gen9, gbl as G
for p in (65521,2147483629,2147483497):
    om=next(pow(g,(p-1)//3,p) for g in range(2,100) if pow(g,(p-1)//3,p)!=1); assert (om*om+om+1)%p==0; om2=om*om%p
    val={'u0':0,'u1':0,'u2':0,'w1':1,'w2':-3,'pp1':0,'pp2':0,'ga2':om2,'ga3':0,'ga4':om,'gb0':0,'gb1':-1,'gb2':-om2,'gb3':0,'gb4':-om,
         'gc2':om,'gc3':0,'gc4':om2,'gd0':0,'gd1':-1,'gd2':-om,'gd3':0,'gd4':-om2}
    for mode in ('LEVEL','FULL'):
        names,eqs,use,nlev=gen9.build('C1G',(0,1,1),p,mode,0)
        pt=[val.get(n,0)%p for n in names]
        def ev(f): 
            s=0
            for k,c in f.items():
                t=c
                for i,e in enumerate(k):
                    if e: t=t*pow(pt[i],e,p)%p
                s=(s+t)%p
            return s
        bad=sum(1 for f in eqs if ev(f)); print('p',p,'mode',mode,'equations',len(eqs),'(level',nlev,') nonzero at M_0:',bad)
