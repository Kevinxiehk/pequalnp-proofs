run() { echo "== KS=$KS $1 $2 $3"; python3 -I eqlm.py $1 $2 "$3" $4 3 80 2>&1 | grep -v identity | tail -${5:-5}; }
export KS=2,3; run 1 Z4 "{(0,):4,(3,):5}" 2
export KS=2,3,4
for kv in "{(0,):4,(3,):5}" "{(0,):5,(3,):4}" "{(0,):4,(1,):1,(3,):4}"; do run 1 Z4 "$kv" 3; done
for kv in "{(1,):5,(2,):4}" "{(1,):5,(0,):2,(2,):2}" ; do run 1 Z5 "$kv" 3; done
export KS=2,3,5
for kv in "{(0,):4,(3,):5}" "{(0,):5,(3,):4}" "{(0,):6,(3,):3}"; do run 1 Z4 "$kv" 3; done
