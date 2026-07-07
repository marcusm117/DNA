import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step10 (ABC : Circle) (a b g : Point)
    (hassump1 : g.isCentre ABC ∧ a.onCircle ABC ∧ b.onCircle ABC) :
    |(g─a)| = |(g─b)| :=
  (point_on_circle_onlyif g a b ABC ⟨hassump1.1, hassump1.2.1, hassump1.2.2⟩).symm

end Elements.Book3
