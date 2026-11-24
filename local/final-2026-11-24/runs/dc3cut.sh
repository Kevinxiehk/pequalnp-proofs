#!/bin/bash
cd /home/kevxhk/work/L-gct-210/verifyfl/r8
one() { F=/home/kevxhk/work/runs/dc3p45/dc_${1}_p2147483629_k3.manifest; ./dc_cut_manifest.sh $F /home/kevxhk/work/runs/dc3p45cut > /home/kevxhk/work/runs/dc3p45cut/dc_${1}_p2147483629_k3.cutlog 2>&1; echo "EXIT $?" >> /home/kevxhk/work/runs/dc3p45cut/dc_${1}_p2147483629_k3.cutlog; }
export -f one
printf "%s\n" p4a p4b p4c p4d | xargs -P 2 -I{} bash -c 'one {}'
echo ALLDONE > /home/kevxhk/work/runs/dc3p45cut/done
