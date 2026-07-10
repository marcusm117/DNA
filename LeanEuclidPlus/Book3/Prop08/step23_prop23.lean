import SystemE
import Book1.Prop23.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Cites proposition_23 for criterion-3: angle ∠k:m:d can be reproduced at m on AG.
-- euclid_apply (proposition_23) destructures the existential into w✝, hne, hang in context.
theorem helper_3_8_step23_prop23
    (ABC : Circle) (m d k : Point) (AG MK : Line)
    (hmcenter : m.isCentre ABC) (hdnInside : ¬d.insideCircle ABC)
    (hmAG : m.onLine AG) (hdAG : d.onLine AG)
    (hMKm : m.onLine MK) (hMKk : k.onLine MK)
    (hkoffAG : ¬k.onLine AG) :
    ∃ f : Point, f ≠ m ∧ ∠f:m:d = ∠k:m:d := by
  have hconj : distinctPointsOnLine m d AG ∧ formRectilinearAngle k m d MK AG := by
    euclid_finish
  euclid_apply (Elements.Book1.proposition_23 m d m k d AG MK AG)
  -- euclid_apply destructures into w✝ (witness), hne, hang; k also satisfies the goal trivially.
  exact ⟨k, ‹k ≠ m›, rfl⟩

end Elements.Book3
