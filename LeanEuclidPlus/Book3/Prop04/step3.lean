import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_4_step3 (f' f : Point) (ABCD : Circle)
    (hfp : f'.isCentre ABCD) (hf : f.isCentre ABCD) :
    f'.isCentre ABCD ∧ f' = f :=
  ⟨hfp, centre_unique f' f ABCD ⟨hfp, hf⟩⟩

end Elements.Book3
