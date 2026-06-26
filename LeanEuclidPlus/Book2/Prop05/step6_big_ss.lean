import SystemE
import Book2.Prop05.step6_big_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub-sub: b.sameSide c EF. b,c lie on AB, parallel to EF (¬EF.intersectsLine AB). First
   EF ≠ AB: e ∈ EF but e ∉ AB (step6_big_eoff, the right-angle degeneracy). Then b,c are off EF
   (a common point of EF and AB would force them to meet, against the parallel) and not separable
   across EF ⟹ same side. b ≠ c from the cut betweenness (between a c d, between c d b ⟹ c ≠ b). -/
theorem helper_2_5_step6_big_ss (a b c d e : Point) (AB EF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b) (hcelen : |(c─e)| = |(c─b)|)
    (hEFAB : ¬(EF.intersectsLine AB)) (hbce : ∠ b:c:e = ∟) :
    b.sameSide c EF := by
  euclid_intros
  have hbc : b ≠ c := by euclid_finish
  have step6_big_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_5_step6_big_eoff b c d e AB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)))
  have hne : EF ≠ AB := fun heq => step6_big_eoff (heq ▸ heEF)
  have hboff : ¬(b.onLine EF) := by
    intro hbon
    euclid_apply (intersection_lines_common_point b EF AB)
    euclid_finish
  have hcoff : ¬(c.onLine EF) := by
    intro hcon
    euclid_apply (intersection_lines_common_point c EF AB)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing b c EF AB)
  euclid_finish

end Elements.Book2
