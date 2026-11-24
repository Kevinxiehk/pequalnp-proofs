#!/bin/bash
# Rebuild lean/fl/FLk.lean, lean/fl/FLl.lean and leanfl/Tps2.lean from the part files.
F=/home/kevxhk/work/L-gct-210/lean/fl; L=/home/kevxhk/work/L-gct-210/leanfl
cd $F || exit 1
OLD="pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1"
R7="x5b tc5c x5c lagcore"
R6="lz lzp p51a p51b p51c p51d x5a"
NEW="sc1a sc1b ps ps4 ps5 np3b ncolp prred pr3a pr3b ps6 pr3c pr3d pr3e ps2 ps3 np3c"
(for p in $OLD; do cat $p.part; done; cat w.tail) > FLk.lean
(for p in $OLD $NEW; do cat $p.part; done; cat w.tail) > FLl.lean
(for p in $OLD $NEW $R6; do cat $p.part; done; cat w.tail) > FLm.lean
(for p in $OLD $NEW $R6 $R7; do cat $p.part; done; cat w.tail) > FLn.lean
(cat pre.part a.part b.part c.part d1.part; echo; cat $L/colsum.snip; echo; cat $L/rowE.snip; echo; cat $L/qA2.snip
 for p in sc1a ps ps4 ps5 np3b ncolp prred pr3a pr3b ps6 p51a x5a; do cat $p.part; done; cat test.tail) > $L/Tps2.lean
wc -lc FLk.lean FLl.lean FLm.lean FLn.lean $L/Tps2.lean
