import SystemE
import Book1.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_hstep4_aux
    (e k l : Point) (EK : Line)
    (hEK : distinctPointsOnLine e k EK)
    (hl_betw : between e l k) :
    ∃ (m0 : Point) (MN : Line),
        ¬(m0.onLine EK) ∧ ∠ e:l:m0 = ∟ ∧ distinctPointsOnLine l m0 MN := by
  euclid_apply (Elements.Book1.proposition_11 e k l EK) as m0
  have hlm0 : l ≠ m0 := by
    intro heq
    subst heq
    exact absurd (show l.onLine EK by euclid_finish) (by assumption)
  euclid_apply (line_from_points l m0) as MN
  exact ⟨m0, MN, by assumption, by assumption, ⟨by assumption, by assumption, hlm0⟩⟩

end Elements.Book3
