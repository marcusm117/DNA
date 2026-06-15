import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.9 sub: c ∉ BE. c lies on AB strictly between a and b (so c ≠ b), and AB meets BE only at b.
   If c ∈ BE then b, c are two distinct shared points of AB and BE ⟹ AB = BE, putting a (∈ AB) on BE
   — contradicting a ∉ BE. -/
theorem helper_2_4_step9_cnbe (a b c : Point) (AB BE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hbBE : b.onLine BE)
    (hanBE : ¬(a.onLine BE)) :
    ¬(c.onLine BE) := by
  intro hcBE
  -- c is on AB (between a and b)
  euclid_apply (between_same_line_in a c b AB)
  -- b, c distinct common points of AB and BE ⟹ AB = BE
  have hbc : b ≠ c := by euclid_finish
  euclid_apply (two_points_determine_line b c AB BE)
  euclid_finish

end Elements.Book2
