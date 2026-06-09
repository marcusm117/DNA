import SystemE
import Book.Prop13
import Book.Prop17

namespace Elements.Book1

/-
Helper for Prop47.lean:89  precondition `between b l' c` of `sum_parallelograms_area`.

`AL` runs through apex `a`, parallel to the square sides `BD` (through b) and `CE`
(through c); `l' = AL ∩ BC`.  Since `AL ⊥ BC` (AL ∥ BD ⊥ BC) the foot `l'` makes a right
angle with `BC` (∠a:l':b = ∠a:l':c = ∟, robustly — supplement of a right angle is right).
With both base angles acute, the foot lands strictly between `b` and `c`.

Proof: negate, case-split the ordering of b,l',c (between_points).  Each bad ordering puts
`l'` outside [b,c]; then proposition_17 (a right angle + a positive angle in the foot
triangle < 2∟) and proposition_13 (straight line) force a base angle > ∟ — contradiction.
-/
theorem helper_47_between_blc :
    ∀ (a b c l' : Point) (AB BC AC BD CE AL : Line),
    a.onLine AB ∧ b.onLine AB ∧
    b.onLine BC ∧ c.onLine BC ∧ b ≠ c ∧
    a.onLine AC ∧ c.onLine AC ∧
    ¬a.onLine BC ∧
    AB ≠ BC ∧ AC ≠ BC ∧
    b.onLine BD ∧ c.onLine CE ∧
    (∠ a:b:c : ℝ) < ∟ ∧ (∠ a:c:b : ℝ) < ∟ ∧
    a.onLine AL ∧ l'.onLine AL ∧ l'.onLine BC ∧
    ¬AL.intersectsLine BD ∧ ¬AL.intersectsLine CE ∧
    ¬BD.intersectsLine CE ∧
    -- AL ⊥ BC at the foot l' (true in Prop47: AL ∥ BD, BD ⊥ BC):
    (∠ a:l':b : ℝ) = ∟ ∧ (∠ a:l':c : ℝ) = ∟ →
    between b l' c :=
by
  euclid_intros
  by_cases hbtw : between b l' c
  · exact hbtw
  · exfalso
    by_cases hb2 : between l' b c
    · -- l' beyond b: foot triangle a-l'-b has right angle at l' ⟹ ∠a:b:l' < ∟,
      --   but l'-b-c straight ⟹ ∠a:b:c = 2∟ - ∠a:b:l' > ∟, contradicting acute.
      euclid_apply (proposition_17 a l' b AL BC AB)
      euclid_apply (proposition_13 a b c l' AB BC)
      euclid_finish
    · -- otherwise the ordering is b-c-l' (c beyond): symmetric at vertex c.
      euclid_apply (proposition_17 a l' c AL BC AC)
      euclid_apply (proposition_13 a c b l' AC BC)
      euclid_finish

end Elements.Book1
