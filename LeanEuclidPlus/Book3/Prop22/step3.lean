import SystemE
import Book3.Prop21.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step3 (a b c d : Point) (ABCD : Circle)
  (ha : a.onCircle ABCD) (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hd : d.onCircle ABCD)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∃ (BC : Line), distinctPointsOnLine b c BC ∧ a.sameSide d BC)   -- "they are in the same segment $BADC$"
  : ∠ c:a:b = ∠ b:d:c := by
  obtain ⟨BC, hbcBC, hadBC⟩ := hassump1
  euclid_apply (proposition_21 a c b d BC ABCD)
  euclid_finish

end Elements.Book3
