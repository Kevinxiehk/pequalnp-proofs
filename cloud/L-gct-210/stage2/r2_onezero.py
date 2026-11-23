# Round 2, item (3): minimal (1,1) pair, kappa has exactly ONE zero entry (column j0), kappa' zero-free.
# Claim (hand proof): the pair data is "Type I_0": E = E1 + E2 (the other four columns), omega = c on E1, -c on E2,
#   nu = kappa|E1, nu' = kappa'|E2 (so nu_j0 = 0: column j0 is FREE in row r), kappa'_j0 arbitrary != 0.
# Checks: (a) every such datum passes the ThB pair test; (b) random perturbations fail; (c) randomized search for other
# solution shapes: sample the finitely many "combinatorial" candidates (rho,rho' patterns on E with values in a small set,
# nu_j0, rho'_j0 in a small set) and list all that pass.
import sys, itertools; sys.path.insert(0,'/home/claude/work/L-gct-210/stage2')
from pairlib import *
rng=np.random.default_rng(2)
def rnd(k): return rng.normal(size=k)+1j*rng.normal(size=k)
def typeI0(kapE,E1mask,kp0,j0=0):
    # columns: j0 first. kap = (0, kapE...), E1mask over the 4 columns of E
    kap=np.concatenate([[0],kapE]); kap=kap/kap.sum()
    m=np.concatenate([[False],E1mask]); m2=np.concatenate([[False],~np.array(E1mask)])
    # kappa' = c*kap on E1, -c*kap on E2, kp0 at j0, sum 1
    K1=kap[m].sum(); K2=kap[m2].sum(); c=(1-kp0)/(K1-K2)
    kapp=np.where(m,c*kap,np.where(m2,-c*kap,0)).astype(complex); kapp[0]=kp0
    nu=np.where(m,kap,0).astype(complex); nup=np.where(m2,kapp,0).astype(complex)
    return kap,kapp,nu,nup
n=0; bad=0
for E1 in itertools.product([True,False],repeat=4):
    if all(E1) or not any(E1): continue
    kap,kapp,nu,nup=typeI0(rnd(4),np.array(E1),rnd(1)[0]); ok,out=pair_check(kap,kapp,nu,nup); ok2,_=gamma_check(kap,kapp,nu,nup); n+=1
    if not (ok and ok2): bad+=1; print('FAIL',E1,[o for o in out if not o[4]])
print('(a) Type I_0 data: %d block choices, failures %d'%(n,bad))
kap,kapp,nu,nup=typeI0(rnd(4),np.array([True,True,False,False]),rnd(1)[0])
nu2=nu.copy(); nu2[0]=0.3; print('(b) nu_j0 != 0 passes?',pair_check(kap,kapp,nu2,nup)[0])
kp2=kapp.copy(); kp2[1]*=1.3; print('(b) omega not +-c passes?',pair_check(kap,kp2,nu,nup)[0])
# (c) combinatorial search: rho, rho' on E with values in {0,1,2,-1}, nu_j0 in {0,1}, rho'_j0 in {0,1}, omega on E in c*{1,-1,i,-i}
vals=[0,1,2]; found={}
cnt=0
for trial in range(1):
    kapE=rnd(4)
    for rho in itertools.product([0,1],repeat=4):
      if rho[0]!=0: continue          # gauge: rho of first E-column = 0
      for rhop in itertools.product(vals,repeat=4):
        for om in itertools.product([1,-1],repeat=4):
          if om[0]!=1: continue
          for nu0 in (0,1):
            for rp0 in (0,1):
              kap=np.concatenate([[0],kapE]); kap=kap/kap.sum(); kp0=0.37+0.21j
              s=(np.array(om)*kap[1:]).sum(); c=(1-kp0)/s
              kapp=np.concatenate([[kp0],c*np.array(om)*kap[1:]])
              nu=np.concatenate([[nu0],np.array(rho)*kap[1:]]); nup=np.concatenate([[rp0*kp0],np.array(rhop)*kapp[1:]])
              # independence
              if rank(np.array([kap,nu]))<2 or rank(np.array([kapp,nup]))<2: continue
              cnt+=1
              if pair_check(kap,kapp,nu,nup)[0]:
                  key=(rho,rhop,om,nu0,rp0); found[key]=1
print('(c) candidates tested:',cnt,' passing:',len(found))
for k in list(found)[:24]: print('   rho',k[0],'rhop',k[1],'omega/c',k[2],'nu_j0',k[3],'rhop_j0',k[4])
