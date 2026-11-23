run() { echo "== $1 $2 $3"; python3 -I eqlm.py $1 $2 "$3" 3 4 60 2>&1 | grep -E "best|start"; }
for g in T Z2b D2 D22; do
  for k1 in 0 1 2 3 4 5 6 7 8; do k0=$((8-k1)); run $g 1 "{(0,):$k0,(1,):$k1}"; done
done
for k1 in 0 1 2 3 4 5; do k0=$((8-k1)); run Z2 1 "{(0,):$k0,(1,):$k1}"; done
