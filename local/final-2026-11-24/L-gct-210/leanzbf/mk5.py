import sys
base, block, out = sys.argv[1], sys.argv[2], sys.argv[3]
t = open(base, encoding='utf-8').read()
b = open(block, encoding='utf-8').read()
endl = '\nend PEqualNP.Outside.L_gct_210_aux.ZBF\n'
assert t.count(endl) == 1
t = t.replace(endl, '\n' + b.strip('\n') + '\n' + endl)
head = 'theorem PEqualNP.Outside.L_gct_210_zbf : '
i = t.index(head)
j = t.index(' := by\n', i)
stmt = t[i+len(head):j]
newhead = 'theorem PEqualNP.Outside.L_gct_210 : (' + stmt + ') ∧ PEqualNP.Outside.L_gct_210_aux.ZBF.T2Hyp ∧ PEqualNP.Outside.L_gct_210_aux.ZBF.T2ppHyp ∧ (PEqualNP.Outside.L_gct_210_aux.ZBF.T1Rest2 → PEqualNP.Outside.L_gct_210_aux.ZBF.T1Hyp) := by\n  refine ⟨?_, PEqualNP.Outside.L_gct_210_aux.ZBF.t2_proof, PEqualNP.Outside.L_gct_210_aux.ZBF.t2pp_proof, PEqualNP.Outside.L_gct_210_aux.ZBF.t1_of_rest2⟩\n'
t = t[:i] + newhead + t[j+len(' := by\n'):]
tmp = out + '.tmp'
open(tmp, 'w', encoding='utf-8').write(t)
import os
os.replace(tmp, out)
print(out, len(t.encode('utf-8')), t.count('\n'))
