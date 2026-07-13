import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step17 (d f b : Point) (ABC : Circle) (DB : Line)
    (h16 : ∀ (p q r : Point) (γ : Circle) (L : Line),
        r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ →
        (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ)
    (h_cen : f.isCentre ABC) (h_b_circ : b.onCircle ABC)
    (h_b_DB : b.onLine DB) (h_d_DB : d.onLine DB) (h_d_noc : ¬ d.onCircle ABC)
    (h14 : ∠ d:b:f = ∟) :
    (∃ p : Point, p.onLine DB ∧ p.onCircle ABC) ∧ ¬ DB.intersectsCircle ABC := by
  apply h16 b d f ABC DB
  euclid_finish

end Elements.Book3
