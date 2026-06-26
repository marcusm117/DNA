import SystemE
import Book2.Prop05.step6_big_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: b ∉ EF. b ∈ AB, EF ∥ AB (¬EF.intersectsLine AB) and EF ≠ AB (e ∈ EF, ¬e ∈ AB via the
   ∠b:c:e degeneracy, step6_big_eoff). A point on AB cannot lie on the parallel EF. -/
theorem helper_2_5_step6_boffef (a b c d e : Point) (AB CE EF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (heEF : e.onLine EF) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hacd : between a c d) (hcdb : between c d b)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ¬(b.onLine EF) := by
  have step6_big_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_5_step6_big_eoff b c d e AB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)))
  intro hbEF
  have hEFneAB : EF ≠ AB := fun heq => step6_big_eoff (heq ▸ heEF)
  euclid_apply (intersection_lines_common_point b EF AB)
  euclid_finish

end Elements.Book2
