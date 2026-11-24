import sympy as sp
za,zb,zc,zk,T,lam=sp.symbols('za zb zc zk T lam')
H={'ea':za**2-T*za-lam,'eb':zb**2-T*zb-lam,'ec':zc**2-T*zc-lam,'ek':zk**2-T*zk+3*lam,'hs':za+zb+zc+zk-T}
def chk(goal, comb, extra):
    d=dict(H); d.update(extra)
    tot=sum(sp.sympify(c)*d[n] for c,n in comb)
    r=sp.expand(goal-tot); assert r==0,(goal,comb,r)
# fab, fac
chk((za-zb)*(za+zb-T),[(1,'ea'),(-1,'eb')],{})
chk((za-zc)*(za+zc-T),[(1,'ea'),(-1,'ec')],{})
# case 1: h1 = za-zb, h2 = za-zc
E={'h1':za-zb,'h2':za-zc}
chk(zk-(T-3*za),[(1,'hs'),(1,'h1'),(1,'h2')],E); E['hzk']=zk-(T-3*za)
chk(za*(2*za-T),[(sp.Rational(1,6),'ek'),(sp.Rational(1,2),'ea'),(-(zk+(T-3*za)-T)/6,'hzk')],E)
E['e1']=za; chk(zb,[(1,'e1'),(-1,'h1')],E); chk(zc,[(1,'e1'),(-1,'h2')],E); chk(zk-T,[(1,'hzk'),(-3,'e1')],E)
E['e1']=2*za-T; chk(za-T/2,[(sp.Rational(1,2),'e1')],E); chk(zb-T/2,[(sp.Rational(1,2),'e1'),(-1,'h1')],E)
chk(zc-T/2,[(sp.Rational(1,2),'e1'),(-1,'h2')],E); chk(zk+T/2,[(1,'hzk'),(-sp.Rational(3,2),'e1')],E)
# case 2: h1 = za-zb, h2 = za+zc-T  -> zc = T-za, zk = -za
E={'h1':za-zb,'h2':za+zc-T}
chk(zk+za,[(1,'hs'),(1,'h1'),(-1,'h2')],E); E['hzk']=zk+za
chk(za*(2*za-T),[(sp.Rational(1,2),'ek'),(sp.Rational(3,2),'ea'),(-(zk-za-T)/2,'hzk')],E)
E['e1']=za; chk(zb,[(1,'e1'),(-1,'h1')],E); chk(zc-T,[(1,'h2'),(-1,'e1')],E); chk(zk,[(1,'hzk'),(-1,'e1')],E)
E['e1']=2*za-T; chk(za-T/2,[(sp.Rational(1,2),'e1')],E); chk(zb-T/2,[(sp.Rational(1,2),'e1'),(-1,'h1')],E)
chk(zc-T/2,[(1,'h2'),(-sp.Rational(1,2),'e1')],E); chk(zk+T/2,[(1,'hzk'),(-sp.Rational(1,2),'e1')],E)
# case 3: h1 = za+zb-T, h2 = za-zc -> zb = T-za, zk = -za
E={'h1':za+zb-T,'h2':za-zc}
chk(zk+za,[(1,'hs'),(-1,'h1'),(1,'h2')],E); E['hzk']=zk+za
chk(za*(2*za-T),[(sp.Rational(1,2),'ek'),(sp.Rational(3,2),'ea'),(-(zk-za-T)/2,'hzk')],E)
E['e1']=za; chk(zb-T,[(1,'h1'),(-1,'e1')],E); chk(zc,[(1,'e1'),(-1,'h2')],E); chk(zk,[(1,'hzk'),(-1,'e1')],E)
E['e1']=2*za-T; chk(za-T/2,[(sp.Rational(1,2),'e1')],E); chk(zb-T/2,[(1,'h1'),(-sp.Rational(1,2),'e1')],E)
chk(zc-T/2,[(sp.Rational(1,2),'e1'),(-1,'h2')],E); chk(zk+T/2,[(1,'hzk'),(-sp.Rational(1,2),'e1')],E)
# case 4: h1 = za+zb-T, h2 = za+zc-T -> zb = zc = T-za, zk = za - T
E={'h1':za+zb-T,'h2':za+zc-T}
chk(zk-(za-T),[(1,'hs'),(-1,'h1'),(-1,'h2')],E); E['hzk']=zk-(za-T)
chk((2*za-T)*(za-T),[(sp.Rational(1,2),'ek'),(sp.Rational(3,2),'ea'),(-(zk+(za-T)-T)/2,'hzk')],E)
E['e1']=2*za-T; chk(za-T/2,[(sp.Rational(1,2),'e1')],E); chk(zb-T/2,[(1,'h1'),(-sp.Rational(1,2),'e1')],E)
chk(zc-T/2,[(1,'h2'),(-sp.Rational(1,2),'e1')],E); chk(zk+T/2,[(1,'hzk'),(sp.Rational(1,2),'e1')],E)
E['e1']=za-T; chk(za-T,[(1,'e1')],E); chk(zb,[(1,'h1'),(-1,'e1')],E); chk(zc,[(1,'h2'),(-1,'e1')],E); chk(zk,[(1,'hzk'),(1,'e1')],E)
print('all ok')
