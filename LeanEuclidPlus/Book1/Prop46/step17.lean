import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step17
    (a b d e : Point)
    (step13 : ∠ b:a:d = ∟)
    (step14 : ∠ a:d:e = ∟)
    (step16 : ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟) :
    ∠ b:a:d = ∟ ∧ ∠ a:d:e = ∟ ∧ ∠ a:b:e = ∟ ∧ ∠ b:e:d = ∟ :=
  ⟨step13, step14, step16.1, step16.2⟩

end Elements.Book1
