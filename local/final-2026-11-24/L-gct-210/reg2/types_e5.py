# Round 15: the explicit list of combinatorial types with e = 5 (NOTES-reg2 23.8): a line pattern (a_0..a_3 | b_0..b_4), each part <= 3,
# sum 5 (full free rows excluded), plus ONE genuine element on a row pair {r,j} or a column pair {a,b} of type R1/C1 (sum-zero) or N (non-sum-
# zero), up to row and column permutations.  Pair positions are distinguished by the line dims of the two rows (columns) involved.
import itertools
pats=set()
for a in itertools.product(range(4),repeat=4):
    for b in itertools.product(range(4),repeat=5):
        if sum(a)+sum(b)!=5: continue
        pats.add((tuple(sorted(a,reverse=True)),tuple(sorted(b,reverse=True))))
types=set()
for (a,b) in pats:
    for r,j in itertools.combinations(range(4),2):
        for g in ('R1','N'): types.add((a,b,'row',tuple(sorted((a[r],a[j]))),g))
    for c,d in itertools.combinations(range(5),2):
        for g in ('C1','N'): types.add((a,b,'col',tuple(sorted((b[c],b[d]))),g))
print('line patterns with e = 5:',len(pats)); print('types (pattern, pair position, genuine type):',len(types))
