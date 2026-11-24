#!/bin/bash
# points of the pair (r,k) third-element variety at fixed t (w as a ring variable with w^2+w+1 = 0), chart XC
r=$1; k=$2; XC=$3; T=$4
cd /home/kevxhk/work/L-gct-210/stage3/r22
f=$(python3 -I kn2_fam.py $r $k $XC); g=${f%.sing}_t${T//\//_}.sing
sed "s/C=C,u0\*(3\*t+2)-1;/C=C,u0*(3*t+2)-1,t-($T),u1,w^2+w+1;/; s/ring R0=(0,w),(/ring R0=0,(w,/; s/ring R=(0,w),(/ring R=0,(w,/; s/minpoly=w^2+w+1;//g" $f | sed 's/^"kn2fam pair.*$/"dim",dim(G),"vdim",vdim(G); if(dim(G)==0){ LIB "solve.lib"; def SOL=solve(G,8,0,"nodisplay"); setring SOL; int ii; int jj; for(ii=1;ii<=size(SOL);ii++){ string ss="PT"; for(jj=1;jj<=size(SOL[ii]);jj++){ ss=ss+" "+string(SOL[ii][jj]); } ss; kill ss; } }/' > $g
grep -o 'ring R=0,([^)]*)' $g | head -1
bash -c "ulimit -v 500000; timeout 60 Singular -q $g" 2>&1 | grep -E "^PT|^dim|error" | head -12
