import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: c ∉ BE. c lies on AB strictly between a and b (so c ≠ b), and AB meets BE only at b.
   If c ∈ BE then b, c are two distinct shared points of AB and BE ⟹ AB = BE, putting a (∈ AB) on BE
   — contradicting a ∉ BE. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step3_cnbe (a b c : Point) (AB BE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hbBE : b.onLine BE)
    (hanBE : ¬(a.onLine BE)) :
    ¬(c.onLine BE) := by
  intro hcBE
  euclid_apply (between_same_line_in a c b AB)
  have hbc : b ≠ c := by euclid_finish
  euclid_apply (two_points_determine_line b c AB BE)
  euclid_finish

end Elements.Book2
