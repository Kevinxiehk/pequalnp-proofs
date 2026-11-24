#!/bin/bash
# usage: liftms.sh FILE.ms OUTPREFIX   -- Singular lift of 1 mod the .ms characteristic; writes OUTPREFIX.cof, prints stats
M=$1; O=$2
V=$(head -1 $M | tr -d ' \r'); C=$(sed -n 2p $M | tr -d ' \r')
tail -n +3 $M | tr -d '\n' > $O.eqs
ulimit -v 500000
/usr/bin/time -f "time %e s maxrss %M KB" timeout ${TL:-600} Singular -q --no-rc <<SING
ring R=$C,($V),dp;
execute("ideal E=" + read("$O.eqs") + ";");
system("--ticks-per-sec",1000); int t0=timer;
ideal Gs = std(E); int t1=timer;
matrix T = lift(E, ideal(1));
int t2=timer;
link l=":w $O.cof"; int i;
for (i=1; i<=ncols(E); i++) { write(l, string(T[i,1])); }
close(l);
int nt=0; int md=0; int ne=0;
for (i=1; i<=ncols(E); i++) { nt = nt + size(T[i,1]); ne = ne + size(E[i]); if (deg(T[i,1])>md) {md=deg(T[i,1]);} }
printf("lift %s: nvars %s neqs %s eqterms %s std ms %s lift ms %s cofterms %s maxdeg %s stdsize %s", "$M", nvars(R), ncols(E), ne, t1-t0, t2-t1, nt, md, size(Gs));
quit;
SING
