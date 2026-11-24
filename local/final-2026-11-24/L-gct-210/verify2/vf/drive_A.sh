#!/bin/bash
# runs own_gen_A.py + msolve on all coordinate charts and on the homogeneous system; prints a summary line per (prime, case)
MS=/usr/bin/msolve
for P in "$@"; do
  for cs in A1 A2 A3 A4 CAL; do
    python3 -I ../own_gen_A.py $P $cs charts own_${P}_$cs 2>/dev/null > list.txt
    unit=0; non=0
    for f in $(cat list.txt); do
      $MS -g 2 -f $f -o $f.out >/dev/null 2>&1
      if tail -n 1 $f.out | grep -q '^\[1\]:'; then unit=$((unit+1)); else non=$((non+1)); fi
    done
    python3 -I ../own_gen_A.py $P $cs hom own_${P}_$cs 2>/dev/null > /dev/null
    $MS -g 2 -f own_${P}_${cs}_hom.ms -o own_${P}_${cs}_hom.out >/dev/null 2>&1
    echo "prime $P case $cs: charts unit $unit, non-unit $non; homogeneous basis: $(grep 'length of basis' own_${P}_${cs}_hom.out | sed 's/#length of basis: *//')"
  done
done
