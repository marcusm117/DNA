import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step18
    (b a e : Point) (BCD : Circle) (AB : Line)
    (step1 : e.isCentre BCD)
    (step16 : ∠ e:b:a = ∟)
    (step17 : b.onCircle BCD)
    (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB)
    (habne : a ≠ b)
    (hassump1 : ∀ (p q r : Point) (γ : Circle) (L : Line),
        r.isCentre γ ∧ p.onCircle γ ∧ distinctPointsOnLine p q L ∧ ∠ r:p:q = ∟ →
        (∃ s : Point, s.onLine L ∧ s.onCircle γ) ∧ ¬ L.intersectsCircle γ)
    : (∃ p : Point, p.onLine AB ∧ p.onCircle BCD) ∧ ¬ AB.intersectsCircle BCD := by
  have hdpq : distinctPointsOnLine b a AB := ⟨hb_AB, ha_AB, habne.symm⟩
  exact hassump1 b a e BCD AB ⟨step1, step17, hdpq, step16⟩

end Elements.Book3
