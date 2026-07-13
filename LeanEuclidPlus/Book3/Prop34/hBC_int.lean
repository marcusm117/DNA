import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_hBC_int (b c₀ p q d1 d d2 : Point) (ABC : Circle) (EF BC : Line)
    (hEF_others : ∀ FA : Line, b.onLine FA → FA ≠ EF → FA.intersectsCircle ABC)
    (hb_BC : b.onLine BC) (hc₀_BC : c₀.onLine BC) (hbc₀ne : b ≠ c₀)
    (hb_EF : b.onLine EF) (hq_EF : q.onLine EF) (hbet_pbq : between p b q)
    (hangle : ∠ c₀:b:q = ∠ d1:d:d2)
    (hlow : 0 < ∠ d1:d:d2) (hhigh : ∠ d1:d:d2 < ∟ + ∟) :
    BC.intersectsCircle ABC := by
  -- c₀ is off the tangent EF (else b, q, c₀ collinear ⟹ ∠ c₀:b:q is 0 or ∟+∟)
  have hc₀_off : ¬ c₀.onLine EF := by
    intro hon
    by_cases hbtw : between c₀ b q
    · euclid_apply (flat_angle_onlyif c₀ b q)
      euclid_finish
    · euclid_apply (degenerated_angle_if b c₀ q EF)
      euclid_finish
  -- hence the chord BC (through c₀) is not the tangent EF, so it meets the circle
  have hBCne : BC ≠ EF := by euclid_finish
  exact hEF_others BC hb_BC hBCne

end Elements.Book3
