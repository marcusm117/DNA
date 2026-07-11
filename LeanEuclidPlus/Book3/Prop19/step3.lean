import SystemE
import Book3.Prop18.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_19_step3 (c f e : Point) (ABC : Circle) (DE : Line)
    (hassump1 : c.onCircle ABC ∧ c.onLine DE ∧ ¬DE.intersectsCircle ABC)
    (hassump2 : f.isCentre ABC ∧ f ≠ c)
    (h_eon : e.onLine DE) (h_enc : e ≠ c) :
    ∠ f:c:e = ∟ := by
  euclid_apply (proposition_18 c f ABC DE)
  euclid_finish

end Elements.Book3
