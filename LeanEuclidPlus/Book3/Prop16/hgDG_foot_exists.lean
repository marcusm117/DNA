import SystemE
import Book1.Prop12.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_hgDG_foot_exists
    (a a' d : Point) (FA : Line)
    (hFAon : a.onLine FA)
    (ha'FA : a'.onLine FA)
    (ha'ne : a ≠ a')
    (hd_off : ¬d.onLine FA)
    : ∃ g : Point, g.onLine FA ∧ (∠ a:g:d = ∟ ∨ ∠ a':g:d = ∟) ∧
        (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟) := by
  obtain ⟨g, hg_on, hg_ang, huniv⟩ :=
    Elements.Book1.proposition_12 a a' d FA ⟨⟨hFAon, ha'FA, ha'ne⟩, hd_off⟩
  exact ⟨g, hg_on, hg_ang, huniv⟩

end Elements.Book3
