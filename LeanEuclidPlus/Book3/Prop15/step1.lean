import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step1
    (e h k b f : Point) (EH EK : Line)
    (hEH : distinctPointsOnLine e h EH)
    (hEK : distinctPointsOnLine e k EK)
    (h_ang_h : ∠ e:h:b = ∟)
    (h_ang_k : ∠ e:k:f = ∟) :
    distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK ∧ ∠ e:h:b = ∟ ∧ ∠ e:k:f = ∟ :=
  ⟨hEH, hEK, h_ang_h, h_ang_k⟩

end Elements.Book3
