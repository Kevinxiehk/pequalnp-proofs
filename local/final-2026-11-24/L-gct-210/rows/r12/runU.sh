#!/bin/bash
# the special line d = u: K_u = span{u e_a, p e_a, u e_b}.  Charts: m_a (all), m_b with m_a = 0, m_c with m_a = m_b = 0 (m_d, m_e by symmetry;
# m two-column on {d,e}: TC5).  Gauges 0/1 (finite chart in al), and the point at infinity Ui.
cd /home/kevxhk/work/L-gct-210/rows/r12
while pgrep -f "[r]unB2.sh" > /dev/null; do sleep 10; done
for f in tU0 tUg0 tUi0 tUz1 tUzg1 tUiz1 tUz2 tUzg2 tUiz2; do (ulimit -v 1500000; /usr/bin/time -f "%e s %M KB" timeout 900 Singular -q $f.sing > $f.out 2>&1); echo "$f: $(grep -v redefin $f.out | grep -E 'gauge|KGEN|halt|KB|rror' | tr '\n' ' ')" >> kU.out; done
echo ALLDONE >> kU.out
