#!/bin/bash
# usage: r11_elim_msolve.sh SCRIPT.sing NT CHAR  -- dump the incidence ideal with Singular, eliminate the first NT variables with msolve (-e NT)
cd /home/kevxhk/work/L-gct-210/stage2/r9
f=$1; nt=$2; ch=$3; b=$(basename $f .sing); d=/tmp/st2_el_$b; mkdir -p $d
sed "s/^int t=timer; ideal G=std(I);.*\$/string vs=varstr(basering); write(\":w $(echo $d | sed 's/\//\\\//g')\/ideal.txt\", vs); write(\":a $(echo $d | sed 's/\//\\\//g')\/ideal.txt\", I);/; /^if(size(G)/d" $f > $d/dump.sing
timeout 300 Singular -q $d/dump.sing > /dev/null 2>&1
python3 -I - "$d" "$ch" <<'PY'
import sys
d,ch=sys.argv[1],sys.argv[2]
txt=open(d+'/ideal.txt').read().strip().split('\n'); vs=txt[0].split(',')
polys=[p.strip() for p in ' '.join(txt[1:]).split(',') if p.strip() and p.strip()!='0']
body=' '.join(polys)
vs=[v for v in vs if v in body]
tv=[v for v in vs if v.startswith('t')]; pv=[v for v in vs if not v.startswith('t')]
open(d+'/in.ms','w').write(','.join(tv+pv)+'\n'+ch+'\n'+',\n'.join(polys)+'\n'); print(len(tv),'eliminated',pv)
PY
timeout 900 msolve -e $(head -1 $d/in.ms | tr ',' '\n' | grep -c '^t') -g 2 -t 2 -f $d/in.ms -o $d/out.txt > $d/log.txt 2>&1
echo "ELIM($b, char $ch): $(grep -v '^#' $d/out.txt | tr -d '\n' | sed 's/,1\*t.*//' | cut -c1-400)"
