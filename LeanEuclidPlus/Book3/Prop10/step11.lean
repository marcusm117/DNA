import SystemE
import Book3.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_10_step11
    (ABC DEF : Circle) (p b : Point)
    (hABCneDEF : ABC ≠ DEF)
    (hbABC : b.onCircle ABC) (hbDEF : b.onCircle DEF)
    (step10 : p.isCentre ABC ∧ p.isCentre DEF)
    : False := by
  have hABCintDEF : ABC.intersectsCircle DEF := by euclid_finish
  have hno_common : ¬ ∃ e : Point, e.isCentre ABC ∧ e.isCentre DEF := by
    euclid_apply (proposition_5 ABC DEF (by assumption) hABCintDEF)
  exact hno_common ⟨p, step10.1, step10.2⟩

end Elements.Book3
