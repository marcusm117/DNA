import SystemE
import Book3.Prop21.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_22_step4 (a b c d : Point) (ABCD : Circle)
  (ha : a.onCircle ABCD) (hb : b.onCircle ABCD) (hc : c.onCircle ABCD) (hd : d.onCircle ABCD)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∃ (AB₀ : Line), distinctPointsOnLine a b AB₀ ∧ c.sameSide d AB₀)   -- "they are in the same segment $ADCB$"
  : ∠ a:c:b = ∠ a:d:b := by
  obtain ⟨AB₀, habAB, hcdAB⟩ := hassump1
  euclid_apply (proposition_21 c a b d AB₀ ABCD)
  euclid_finish

end Elements.Book3
