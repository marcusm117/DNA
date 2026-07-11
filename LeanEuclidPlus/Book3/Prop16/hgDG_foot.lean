import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_16_hgDG_foot
    (a a' d : Point) (FA AE : Line) (e b : Point)
    (hFAon : a.onLine FA)
    (ha'FA : a'.onLine FA)
    (ha'ne : a ≠ a')
    (hd_off : ¬d.onLine FA)
    (hFAne : FA ≠ AE)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (right_6 : a ≠ e)
    (hgDG_foot_exists : ∃ g : Point, g.onLine FA ∧ (∠ a:g:d = ∟ ∨ ∠ a':g:d = ∟) ∧
        (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟))
    : ∃ g, g.onLine FA ∧ ∠ a:g:d = ∟ := by
  obtain ⟨g, hgFA, hgperp, huniv⟩ := hgDG_foot_exists
  have hdg : d ≠ g := fun heq => hd_off (heq ▸ hgFA)
  obtain ⟨DG_line, hDGd, hDGg⟩ := line_from_points d g hdg
  refine ⟨g, hgFA, ?_⟩
  cases hgperp with
  | inl h => exact h
  | inr h =>
    by_cases hag : a = g
    · -- dag case: exfalso via two perpendiculars at same vertex → FA = AE, contradiction
      have hgDG_foot_inr_dag : ∠ a:g:d = ∟ := by sorry
      exact hgDG_foot_inr_dag
    · -- a ≠ g: proposition_12 universality gives ∠a:g:d=∟ directly
      exact huniv a hFAon hag

end Elements.Book3
