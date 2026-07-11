import SystemE
import Book3.Prop16.hgDG_foot_exists
import Book3.Prop16.hgDG_foot
import Book3.Prop16.hgDG_agne
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

theorem helper_3_16_hgDG
    (a d : Point) (ABC : Circle) (FA AE : Line) (e b : Point)
    (left : d.isCentre ABC)
    (hFAon : a.onLine FA)
    (hFAnot : ¬FA.intersectsCircle ABC)
    (hFAne : FA ≠ AE)
    (left_3 : between a d b)
    (right_4 : ∠ e:a:b = ∟)
    (left_5 : a.onLine AE)
    (left_6 : e.onLine AE)
    (right_6 : a ≠ e)
    : ∃ (g : Point) (DG_line : Line),
        g.onLine FA ∧ ∠ a:g:d = ∟ ∧ d.onLine DG_line ∧ g.onLine DG_line ∧ a ≠ g := by
  have hd_inside : d.insideCircle ABC := center_inside_circle d ABC left
  have hd_off : ¬d.onLine FA := fun hd_on =>
    hFAnot (intersection_circle_line_2 d ABC FA ⟨hd_inside, hd_on⟩)
  obtain ⟨a', ha'ne, ha'FA⟩ := exists_distincts_points_on_line FA a
  have hgDG_foot_exists : ∃ g : Point, g.onLine FA ∧ (∠ a:g:d = ∟ ∨ ∠ a':g:d = ∟) ∧
      (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟) := by euclid_apply (helper_3_16_hgDG_foot_exists a a' d FA (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show a'.onLine FA; assumption)) (by euclid_assumption "" (show a ≠ a'; assumption)) (by euclid_assumption "" (show ¬d.onLine FA; assumption)))
  have hgDG_foot : ∃ g, g.onLine FA ∧ ∠ a:g:d = ∟ ∧
      (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟) := by euclid_apply (helper_3_16_hgDG_foot a a' d FA AE e b (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show a'.onLine FA; assumption)) (by euclid_assumption "" (show a ≠ a'; assumption)) (by euclid_assumption "" (show ¬d.onLine FA; assumption)) (by euclid_assumption "" (show FA ≠ AE; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show ∃ g : Point, g.onLine FA ∧ (∠ a:g:d = ∟ ∨ ∠ a':g:d = ∟) ∧ (∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟); assumption)))
  obtain ⟨g, hgFA, hang, huniv⟩ := hgDG_foot
  have hdg : d ≠ g := fun h => hd_off (h ▸ hgFA)
  obtain ⟨DG_line, hDGd, hDGg⟩ := line_from_points d g hdg
  have hgDG_agne : a ≠ g := by euclid_apply (helper_3_16_hgDG_agne a a' d g FA AE DG_line e b (by euclid_assumption "" (show a.onLine FA; assumption)) (by euclid_assumption "" (show a'.onLine FA; assumption)) (by euclid_assumption "" (show a ≠ a'; assumption)) (by euclid_assumption "" (show ¬d.onLine FA; assumption)) (by euclid_assumption "" (show FA ≠ AE; assumption)) (by euclid_assumption "" (show between a d b; assumption)) (by euclid_assumption "" (show ∠ e:a:b = ∟; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)) (by euclid_assumption "" (show d.onLine DG_line; assumption)) (by euclid_assumption "" (show g.onLine DG_line; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine FA → p ≠ g → ∠ p:g:d = ∟; assumption)))
  exact ⟨g, DG_line, hgFA, hang, hDGd, hDGg, hgDG_agne⟩

end Elements.Book3
