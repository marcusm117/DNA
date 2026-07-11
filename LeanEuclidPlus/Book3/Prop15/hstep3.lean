import SystemE
import Book1.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_hstep3
    (e h k : Point) (EH EK : Line)
    (hEH : distinctPointsOnLine e h EH)
    (hEK : distinctPointsOnLine e k EK)
    (h_step2 : |(e─k)| > |(e─h)|) :
    ∃ l : Point, between e l k ∧ |(e─l)| = |(e─h)| := by
  euclid_apply (Elements.Book1.proposition_3 e k e h EK EH) as l
  exact ⟨l, by assumption, by assumption⟩

end Elements.Book3
