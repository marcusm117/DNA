import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12 sub-sub: c.sameSide d AK. a ∈ AK is the foot of AB; between a c d puts c,d on the same
   ray from a, hence the same side of AK (pasch_2). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12_sshc_cd (a c d : Point) (AB AK : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (haAK : a.onLine AK)
    (hacd : between a c d)
    (hAKAB : AK ≠ AB) :
    c.sameSide d AK := by
  euclid_intros
  have hcoffAK : ¬(c.onLine AK) := by
    intro hon; euclid_apply (intersection_lines_common_point c AK AB); euclid_finish
  euclid_apply (pasch_2 a c d AK)
  euclid_finish

end Elements.Book2
