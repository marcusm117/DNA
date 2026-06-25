import SystemE
import Book2.Prop07.step3_cnad
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub-sub: a and d are on the same side of CN. Both lie on AD, which does not cross CN.
   c distinguishes the lines: c ∈ CN, but c ∉ AD (step3_cnad), so CN ≠ AD; then a, d are off CN
   (a shared point of two distinct lines makes them intersect); finally a, d off CN on a line
   parallel to CN lie on the same side. -/
theorem helper_2_7_step3_bgd_ss (a b c d : Point) (AB CN AD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟)
    (hCNAD : ¬(CN.intersectsLine AD)) :
    a.sameSide d CN := by
  euclid_intros
  have step3_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_7_step3_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hne : CN ≠ AD := by
    intro heq; rw [heq] at hcCN; exact step3_cnad hcCN
  have haoff : ¬(a.onLine CN) := by
    intro hon
    euclid_apply (intersection_lines_common_point a CN AD)
    euclid_finish
  have hdoff : ¬(d.onLine CN) := by
    intro hon
    euclid_apply (intersection_lines_common_point d CN AD)
    euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a d CN AD)
  euclid_apply (intersection_symm CN AD)
  euclid_finish

end Elements.Book2
