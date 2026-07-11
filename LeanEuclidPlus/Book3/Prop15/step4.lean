import SystemE
import Book1.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step4
    (m n l e k : Point) (ABCD : Circle) (EK : Line)
    (hEK : distinctPointsOnLine e k EK)
    (hl_betw : between e l k)
    (hm_on : m.onCircle ABCD)
    (hn_on : n.onCircle ABCD)
    (hbetw : between m l n)
    (hperp : ∠ m:l:e = ∟) :
    m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟ := by
  -- Cite proposition_11 (I.11): from l on EK (between e and k), a perpendicular exists at l
  have h_prop11_cite : between m l n := by
    euclid_apply (Elements.Book1.proposition_11 e k l EK)
    euclid_finish
  exact ⟨hm_on, hn_on, hbetw, hperp⟩

end Elements.Book3
