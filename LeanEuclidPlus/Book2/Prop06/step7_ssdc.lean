import SystemE
import Book2.Prop06.step2_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub-sub: d.sameSide c EF. d,c lie on AB, which is parallel to EF (¬EF.intersectsLine AB).
   First EF ≠ AB: e ∈ EF, but e ∉ AB (step7_eoff, the right-angle degeneracy). Then d,c are off EF
   (a common point of EF and AB would force them to meet, against the parallel), and not separable
   across EF ⟹ same side. d ≠ c from between a c b / between a b d (c between a,b; d beyond b). -/
theorem helper_2_6_step7_ssdc (a b c d e : Point) (AB EF CE : Line)
    (hdAB : d.onLine AB) (hcAB : c.onLine AB)
    (heEF : e.onLine EF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|)
    (hEFAB : ¬(EF.intersectsLine AB)) (hdce : ∠ d:c:e = ∟) :
    d.sameSide c EF := by
  euclid_intros
  have hdc : d ≠ c := by euclid_finish
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hne : EF ≠ AB := fun heq => step2_eoff (heq ▸ heEF)
  have hdoff : ¬(d.onLine EF) := by
    intro hdon
    euclid_apply (intersection_lines_common_point d EF AB)
    euclid_finish
  have hcoff : ¬(c.onLine EF) := by
    intro hcon
    euclid_apply (intersection_lines_common_point c EF AB)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing d c EF AB)
  euclid_finish

end Elements.Book2
