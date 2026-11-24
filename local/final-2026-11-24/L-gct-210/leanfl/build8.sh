#!/bin/bash
# Round 8: build lean/fl/FLo.lean (= FLn parts + R8) and leanfl/Tr8.lean only; leaves FLk..FLn untouched.
F=/home/kevxhk/work/L-gct-210/lean/fl; L=/home/kevxhk/work/L-gct-210/leanfl
cd $F || exit 1
OLD="pre a b c d1 e f g h j k o2 p i5 l2 m n r1 r2 s1 s2 s3 t3 ds x1 x2 x3 y1 x4 n1 n2 z1 z2 q1 r4 r5 f1 g1 h1"
NEW="sc1a sc1b ps ps4 ps5 np3b ncolp prred pr3a pr3b ps6 pr3c pr3d pr3e ps2 ps3 np3c"
R6="lz lzp p51a p51b p51c p51d x5a"
R7="x5b tc5c x5c lagcore"
R8="lag nbcore nb p1 p1b p1c p2 nbl nbq"
R9="p3a p3b p3c p4a p4b"
R10="p4c p4d p4e p4f p4g p4h p4i p4j p4k"
R11="p5a p5b p5c p5d p5e p5f p5g p5h p5i p5j p5k p5l p5m p5n p5o p5p p5q p5r p5s p5t p5u p5v p5w p5x p5y p5z p5aa p5ab p5ac p5ad"
(for p in $OLD $NEW $R6 $R7 $R8 $R9; do cat $p.part; done; cat w.tail) > FLo.lean
(for p in $OLD $NEW $R6 $R7 $R8 $R9 $R10; do cat $p.part; done; cat w.tail) > FLp.lean
(for p in $OLD $NEW $R6 $R7 $R8 $R9 $R10 $R11; do cat $p.part; done; cat w.tail) > FLq.lean.new && mv FLq.lean.new FLq.lean
X=$L/extract.py
python3 -I $X z2.part uY dY > $L/uYdY.snip || exit 1
python3 -I $X p51d.part span2_perp > $L/span2.snip || exit 1
python3 -I $X p1.part e2_ip LAG_line zeta_span > $L/p1gen.snip || exit 1
python3 -I $X p1b.part uYL uYL_apply dYL dYL_apply mL mL_apply uY_dY_zero iso_image line_quad prod_lin eps_of line_exp > $L/p1bgen.snip || exit 1
python3 -I $X p1c.part chi_pow iso_quad > $L/p1cgen.snip || exit 1
(cat pre.part a.part b.part c.part d1.part; echo; cat $L/e2.snip; echo; cat $L/e2b.snip; echo; cat $L/Qv.snip; echo
 cat $L/uYdY.snip $L/span2.snip
 for p in lagcore lag nbcore; do cat $p.part; done; echo; cat $L/p1gen.snip $L/p1bgen.snip $L/p1cgen.snip; cat test.tail) > $L/Tr8.lean
for G in FLo.lean FLp.lean FLq.lean $L/Tr8.lean; do
  echo "$G: $(wc -lc < $G) add $(grep -cE '^[[:space:]]*add_' $G) quotes $(grep -c '"' $G) hash $(grep -c '#' $G) banned $(grep -cE 'sorry|axiom|native_decide|initialize|macro|syntax|notation|elab|attribute|instance|structure|inductive' $G) comments $(grep -cE -- '--|/-' $G) dupnames $(grep -E '^(theorem|def) ' $G | awk '{print $2}' | sort | uniq -d | wc -l)"
done
# dependency-closure test file for all R8 parts (needed blocks of the FLn parts only)
# Tr8full.lean is FROZEN (window 2 compiles it); regenerate only deliberately
python3 -I $L/closure.py $F "$OLD $NEW $R6 $R7 $R8" "$R9" $L/Tr9.lean
python3 -I $L/closure.py $F "$OLD $NEW $R6 $R7 $R8 $R9" "$R10" $L/Tr10.lean
python3 -I $L/closure.py $F "$OLD $NEW $R6 $R7 $R8 $R9 $R10" "$R11" $L/Tr11.lean.new && mv $L/Tr11.lean.new $L/Tr11.lean
for G in $L/Tr9.lean $L/Tr10.lean $L/Tr11.lean; do
echo "$G: $(wc -lc < $G) add $(grep -cE '^[[:space:]]*add_' $G) quotes $(grep -c '"' $G) hash $(grep -c '#' $G) banned $(grep -cE 'sorry|axiom|native_decide|initialize|macro|syntax|notation|elab|attribute|instance|structure|inductive' $G) comments $(grep -cE -- '--|/-' $G) dupnames $(grep -E '^(theorem|def|abbrev) ' $G | awk '{print $2}' | sort | uniq -d | wc -l)"
done
# round-13 parts (c1 + TC5_final) with their closure
python3 -I $L/closure.py $F "$OLD $NEW $R6 $R7 $R8 $R9 $R10 p5a p5b p5c p5d p5e p5f p5g p5h p5i p5j p5k p5l p5m p5n" "p5o p5p p5q p5r p5s p5t p5u p5v p5w p5x p5y p5z p5aa p5ab p5ac p5ad" $L/Tr13.lean.new && mv $L/Tr13.lean.new $L/Tr13.lean
