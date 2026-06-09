import SystemE
import Book.Helper47_c_sameSide_a_BF   -- provides helper_47_sameSide_perp

namespace Elements.Book1

/-
Helper for Prop47.lean:59  `e.sameSide b AC`.
Square BCDE on BC, opposite side from a; extend a─c to c' with exterior ∠b:c:c' > ∟.
Base angle ∠a:c:b < ∟, ∠b:c:e = ∟, so ray c→e stays on b's side of AC.
-/
theorem helper_47_e_sameSide_b_AC :
    ∀ (a b c d e c' : Point) (AB BC AC BD CE DE : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    b.onLine BC ∧ c.onLine BC ∧
    a.onLine AC ∧ c.onLine AC ∧
    AB ≠ BC ∧ BC ≠ AC ∧ AC ≠ AB ∧
    (∠ b:a:c : ℝ) = ∟ ∧
    (∠ a:c:b : ℝ) < ∟ ∧
    ¬e.onLine AC ∧
    b.onLine BD ∧ d.onLine BD ∧
    c.onLine CE ∧ e.onLine CE ∧
    d.onLine DE ∧ e.onLine DE ∧
    (∠ c:b:d : ℝ) = ∟ ∧ (∠ b:c:e : ℝ) = ∟ ∧
    (∠ b:d:e : ℝ) = ∟ ∧ (∠ c:e:d : ℝ) = ∟ ∧
    ¬d.sameSide a BC ∧
    ¬DE.intersectsLine BC ∧ ¬BD.intersectsLine CE ∧
    c'.onLine AC ∧ between a c c' ∧
    (∠ b:c:c' : ℝ) > ∟ →
    e.sameSide b AC :=
by
  euclid_intros
  -- Step 1: a.sameSide b CE  (perpendicular lemma: CE⊥BC at c, acute ∠a:c:b)
  euclid_apply (helper_47_sameSide_perp a b c e BC CE)
  -- Step 2: e.sameSide b AC  (triple_incidence_2 on lines CE,BC,AC at c)
  euclid_apply (triple_incidence_2 CE BC AC c e b a)
  euclid_finish

end Elements.Book1