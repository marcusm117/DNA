import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: c ∉ BE. c lies on AB strictly between a and b (so c ≠ b), and AB meets BE only at b.
   If c ∈ BE then b, c are two distinct shared points of AB and BE ⟹ AB = BE, putting a (∈ AB) on BE
   — contradicting a ∉ BE. -/
theorem helper_2_7_step3_cnbe (a b c e : Point) (AB BE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hab : a ≠ b) (heb : e ≠ b) (habe : ∠ a:b:e = ∟) :
    ¬(c.onLine BE) := by
  have hanBE : ¬(a.onLine BE) := by
    intro haBE
    euclid_finish
  intro hcBE
  euclid_apply (between_same_line_in a c b AB)
  have hbc : b ≠ c := by euclid_finish
  euclid_apply (two_points_determine_line b c AB BE)
  euclid_finish

end Elements.Book2
