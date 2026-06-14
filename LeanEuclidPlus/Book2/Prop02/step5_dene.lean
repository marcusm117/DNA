import SystemE
import Book2.Prop02.step5_doff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.2.5: DE ≠ AB. d lies on DE but not on AB (step5_doff, from the right angle
   ∠b:a:d), so the two lines differ. -/
theorem helper_2_2_step5_dene (a b c d : Point) (AB DE AD : Line)
    (hbad : ∠ b:a:d = ∟) (had : a ≠ d) (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdDE : d.onLine DE)
    (hdAD : d.onLine AD) (haAD : a.onLine AD) :
    DE ≠ AB := by
  euclid_intros
  have step5_doff : ¬(d.onLine AB) := by euclid_apply (helper_2_2_step5_doff a b c d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
