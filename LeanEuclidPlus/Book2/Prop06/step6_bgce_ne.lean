import SystemE
import Book2.Prop06.step2_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_sslc: BG ≠ CE. b is on BG; b ∉ CE (else b and c, distinct points on
   AB, both lie on CE so CE = AB (two_points_determine_line), putting e ∈ AB and degenerating the
   right angle ∠d:c:e = ∟ — captured by reusing step2_eoff for e ∉ AB). So BG ≠ CE via b. -/
theorem helper_2_6_step6_bgce_ne (a b c d e : Point) (AB CE BG : Line)
    (hbBG : b.onLine BG)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    BG ≠ CE := by
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have hboff : ¬(b.onLine CE) := by
    intro hbCE
    euclid_apply (two_points_determine_line b c CE AB)
    euclid_finish
  intro h
  rw [h] at hbBG
  exact hboff hbBG

end Elements.Book2
