import SystemE
import Book.Prop15
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_28_step1_assumption2 (a b d e f g h : Point) (AB EF : Line)
    (haonAB : a.onLine AB) (hbonAB : b.onLine AB) (hab : a ≠ b)
    (heonEF : e.onLine EF) (hfonEF : f.onLine EF) (hef : e ≠ f)
    (hbet_ab : between a g b)
    (hbet_eh : between e g h)
    (hbet_ghf : between g h f)
    (hsameside : b.sameSide d EF) :
    ∠ e:g:b = ∠ a:g:h := by
  have hAB : distinctPointsOnLine a b AB := ⟨haonAB, hbonAB, hab⟩
  have hEF : distinctPointsOnLine e f EF := ⟨heonEF, hfonEF, hef⟩
  have hne : AB ≠ EF := by
    intro heq
    have hbonEF : b.onLine EF := heq ▸ hbonAB
    exact same_side_not_on_line b d EF hsameside hbonEF
  euclid_apply (proposition_15 a b e h g AB EF)
  euclid_finish

end Elements.Book1
