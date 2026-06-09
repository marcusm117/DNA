import SystemE
import Book.Prop17
import Book.Helper47_c_sameSide_a_BF

namespace Elements.Book1

/-
Helper for Prop47.lean:69  `(∠ d:b:a : ℝ) = ∠ f:b:c`.
Square ABFG on AB (∠a:b:f = ∟, f off AB opposite c); square BCDE on BC (∠c:b:d = ∟,
d off BC opposite a).  Both ∠d:b:a and ∠f:b:c equal ∟ + ∠a:b:c.
d on BD (through b); f on BF (through b).
-/
theorem helper_47_angle_dba_eq_fbc :
    ∀ (a b c d f : Point) (AB BC AC BD BF : Line),
    -- triangle abc with the right angle at a (the governing Prop47 premise):
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    b.onLine BC ∧ c.onLine BC ∧ b ≠ c ∧
    a.onLine AC ∧ c.onLine AC ∧ a ≠ c ∧
    AB ≠ BC ∧ BC ≠ AC ∧ AC ≠ AB ∧
    (∠ b:a:c : ℝ) = ∟ ∧
    ¬c.onLine AB ∧ ¬a.onLine BC ∧
    ¬f.onLine AB ∧ ¬d.onLine BC ∧
    ¬f.sameSide c AB ∧
    ¬d.sameSide a BC ∧
    -- construction data Prop47 has (this✝² @ line 69) but the trimmed context can't re-derive:
    d.sameSide c AB ∧
    b.onLine BD ∧ d.onLine BD ∧
    b.onLine BF ∧ f.onLine BF ∧
    (∠ a:b:f : ℝ) = ∟ ∧
    (∠ c:b:d : ℝ) = ∟ →
    (∠ d:b:a : ℝ) = (∠ f:b:c : ℝ) :=
by
  euclid_intros
  -- (1) acuteness at b, from prop17 + right angle at a (mirrors Prop47:26-28)
  euclid_apply (proposition_17 c a b AC AB BC)
  have hAcuteB : (∠ a:b:c : ℝ) < ∟ := by euclid_finish
  -- (2) acuteness at c, symmetric (mirrors Prop47:44-46)
  euclid_apply (proposition_17 b c a BC AC AB)
  have hAcuteC : (∠ a:c:b : ℝ) < ∟ := by euclid_finish
  -- (3) the four sameSide preconditions of the two splits.
  --   hA11, hC11 (orig point vs square side): derivable & fast.
  --   hA10, hC10 (square corner vs orig line): NOT derivable from this context (construction data).
  have hA11 : a.sameSide c BD := by euclid_finish
  have hC11 : c.sameSide a BF := by
    euclid_apply (helper_47_sameSide_perp c a b f AB BF)
    euclid_finish
  have hA10 : d.sameSide c AB := by euclid_finish
  -- hC10 from triple_incidence_2 (lines BF,AB,BC at b): consumes hC11 (a.sameSide c BF),
  -- ¬f.sameSide c AB, ¬c.onLine AB, f≠b ⟹ f.sameSide a BC.  No circularity.
  have hC10 : f.sameSide a BC := by
    euclid_apply (triple_incidence_2 BF AB BC b f a c)
    euclid_finish
  -- (4) the two splits + arithmetic
  euclid_apply sum_angles_onlyif b d a c BD AB
  euclid_apply sum_angles_onlyif b f c a BF BC
  euclid_finish


end Elements.Book1
