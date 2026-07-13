import SystemE
import Book1.Prop15.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_34_hef_choice (b c c₀ p q d1 d d2 : Point) (ABC : Circle) (EF BC : Line)
    (hp_EF : p.onLine EF) (hq_EF : q.onLine EF) (hbet_pbq : between p b q)
    (hb_EF : b.onLine EF) (hb_BC : b.onLine BC) (hc₀_BC : c₀.onLine BC) (hc_BC : c.onLine BC)
    (hbc_ne : b ≠ c) (hbc₀ne : b ≠ c₀)
    (hangle : ∠ c₀:b:q = ∠ d1:d:d2)
    (hBC_int : BC.intersectsCircle ABC) (hEF_notint : ¬ EF.intersectsCircle ABC) :
    ∃ e f : Point, e.onLine EF ∧ f.onLine EF ∧ between e b f ∧ ∠ f:b:c = ∠ d1:d:d2 := by
  have hBCneEF : BC ≠ EF := by euclid_finish
  by_cases hbtw : between c b c₀
  · -- c is on the ray opposite c₀ from b: f = p (∠ p:b:c is vertical to ∠ c₀:b:q)
    euclid_apply (proposition_15 p q c₀ c b EF BC)
    exact ⟨q, p, hq_EF, hp_EF, by euclid_finish, by euclid_finish⟩
  · -- c is on the same ray as c₀ from b: f = q, angle unchanged
    euclid_apply (equal_angles b q q c c₀ EF BC)
    exact ⟨p, q, hp_EF, hq_EF, hbet_pbq, by euclid_finish⟩

end Elements.Book3
