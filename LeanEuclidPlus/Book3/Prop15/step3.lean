import SystemE
import Book1.Prop03.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step3
    (e h k l : Point) (EH EK : Line)
    (hEH : distinctPointsOnLine e h EH)
    (hEK : distinctPointsOnLine e k EK)
    (h_step2 : |(e─k)| > |(e─h)|)
    (hl_eq : |(e─l)| = |(e─h)|) :
    |(e─l)| = |(e─h)| := by
  -- Cite proposition_3 (I.3): EL can be cut from EK equal to EH (the existence of l')
  have h_prop3_cite : |(e─h)| < |(e─k)| := by
    euclid_apply (Elements.Book1.proposition_3 e k e h EK EH)
    linarith
  exact hl_eq

end Elements.Book3
