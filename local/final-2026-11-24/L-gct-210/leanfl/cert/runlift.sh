#!/bin/bash
# usage: runlift.sh EQSFILE CHAR NVARS OUTFILE  (Singular lift of 1 in the ideal; cofactors one per line)
E=$1; C=$2; N=$3; O=$4
V=$(python3 -I -c "print(','.join('t%d'%i for i in range($N)))")
ulimit -v 500000
timeout 1800 Singular -q --no-rc <<SING
ring R=$C,($V),dp;
execute("ideal E=" + read("$E") + ";");
int t0=timer; system("--ticks-per-sec",1000); t0=timer;
matrix T = lift(E, ideal(1));
int t1=timer;
poly chk = 0; int i;
for (i=1; i<=ncols(E); i++) { chk = chk + E[i]*T[i,1]; }
link l=":w $O"; 
for (i=1; i<=ncols(E); i++) { write(l, string(T[i,1])); }
close(l);
int nt=0; int md=0;
for (i=1; i<=ncols(E); i++) { nt = nt + size(T[i,1]); if (deg(T[i,1])>md) {md=deg(T[i,1]);} }
printf("lift %s char %s: check %s, ms %s, terms %s, maxdeg %s", "$E", "$C", chk==1, t1-t0, nt, md);
quit;
SING
