#!/bin/bash
# usage: elim.sh SCRIPT NT  -> eliminate the first NT ring variables (the t's) and print minimal associated primes of the parameter locus
ulimit -v 2500000
f=$1; nt=$2
sed "s/^int t=timer; ideal G=std(I);.*\$/int t=timer; poly tt=1; int ii; for(ii=1;ii<=$nt;ii++){tt=tt*var(ii);} ideal E=eliminate(I,tt); E=std(E); \"ELIM\"; E; LIB \"primdec.lib\"; list L=minAssGTZ(E); \"PRIMES\"; L; \"sec\",timer-t;/; /^if(size(G)/d" $f > ${f%.sing}_elim.sing
timeout ${TMO:-900} Singular -q ${f%.sing}_elim.sing 2>&1
