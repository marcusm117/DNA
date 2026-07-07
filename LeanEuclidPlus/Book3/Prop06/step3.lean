import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step3 (ABC CDE : Circle) (b e f : Point) (FEB : Line)
    (hbABC : b.onCircle ABC) (heCDE : e.onCircle CDE)
    (hfFEB : f.onLine FEB) (heFEB : e.onLine FEB) (hbFEB : b.onLine FEB)
    : b.onCircle ABC ∧ e.onCircle CDE ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB :=
  ⟨hbABC, heCDE, hfFEB, heFEB, hbFEB⟩

end Elements.Book3
