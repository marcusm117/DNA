import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step9
    (k m g h : Point) (GH : Line)
    (hk_not_GH : ¬k.onLine GH)
    (hm_not_GH : ¬m.onLine GH)
    (hms_k : ¬m.sameSide k GH)
    (step8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) :
    k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) :=
  ⟨⟨hk_not_GH, hm_not_GH, fun hss => hms_k (same_side_symm k m GH hss)⟩, step8⟩

end Elements.Book1
