for a in "3,0,0,0,0" "2,1,0,0,0" "1,1,1,0,0"; do for b in "4,0,0,0,0" "3,1,0,0,0" "2,2,0,0,0" "2,1,1,0,0" "1,1,1,1,0"; do nice -n 5 python3 -I prodlm.py $a $b 3 9 45 2>&1 | grep rows; done; done
