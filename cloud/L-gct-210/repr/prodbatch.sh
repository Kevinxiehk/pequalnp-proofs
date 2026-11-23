P4=("4,0,0,0,0" "3,1,0,0,0" "2,2,0,0,0" "2,1,1,0,0" "1,1,1,1,0")
P3=("3,0,0,0,0" "2,1,0,0,0" "1,1,1,0,0")
echo "### K=8 (4|4)"
for a in "${P4[@]}"; do for b in "${P4[@]}"; do python3 -I prodlm.py $a $b 4 7 70 2>&1 | grep rows; done; done
echo "### K=7 (3|4)"
for a in "${P3[@]}"; do for b in "${P4[@]}"; do python3 -I prodlm.py $a $b 3 7 70 2>&1 | grep rows; done; done
