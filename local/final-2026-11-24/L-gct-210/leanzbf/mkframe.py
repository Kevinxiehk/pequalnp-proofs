import sys, os
frame, r4, out = sys.argv[1], sys.argv[2], sys.argv[3]
F = open(frame, encoding='utf-8').read().split('\n')
kit_start = F.index('namespace PEqualNP.Gct.MethodCeiling')
kit_end = F.index('end PEqualNP.Gct.F210')
kit = '\n'.join(F[kit_start:kit_end+1])
for nm in ['MethodCeiling', 'Helpers.Minc', 'Helpers.RankOne', 'Kit086', 'F210']:
    kit = kit.replace('PEqualNP.Gct.' + nm, 'PEqualNP.Outside.L_gct_210_aux.' + nm)
assert 'PEqualNP.Gct.' not in kit.replace('PEqualNP.Gct.permPoly', '')
R = open(r4, encoding='utf-8').read()
z0 = R.index('namespace PEqualNP.Outside.L_gct_210_aux.ZBF')
z1 = R.index('end PEqualNP.Outside.L_gct_210_aux.ZBF') + len('end PEqualNP.Outside.L_gct_210_aux.ZBF')
zbf = R[z0:z1]
final = R[R.index('theorem PEqualNP.Outside.L_gct_210 :'):]
bridge = '''namespace PEqualNP.Outside.L_gct_210_aux.Bridge

theorem lev_iff_F210 (n : ℕ) (L : Submodule ℂ (Fin n × Fin n → ℂ)) :
    PEqualNP.Outside.L_gct_210_aux.ZBF.Lev n L ↔ PEqualNP.Outside.L_gct_210_aux.F210.Lev n L :=
  Iff.rfl

end PEqualNP.Outside.L_gct_210_aux.Bridge'''
t = 'import Mathlib\nimport PEqualNP.Defs\n\n' + kit + '\n\n' + zbf + '\n\n' + bridge + '\n\n' + final
tmp = out + '.tmp'
open(tmp, 'w', encoding='utf-8').write(t)
os.replace(tmp, out)
print(out, len(t.encode('utf-8')), t.count('\n'))
