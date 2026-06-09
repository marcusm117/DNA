import SystemE
import Book.Prop29

namespace Elements.Book1

/-
Sub-lemma for `helper_47_between_blc`:  AL ∥ BD and BD ⊥ BC (∠c:b:d = ∟) ⟹ AL ⊥ BC,
i.e. the foot l' = AL ∩ BC makes a right angle:  ∠a:l':b = ∟.

Proof: proposition_29''' on parallels AL, BD with transversal BC (meeting at l', b) gives the
alternate-angle equality ∠a:l':b = ∠l':b:d; since l' lies on BC (ray from b toward c or its
opposite), ∠l':b:d = ∠c:b:d = ∟.
-/
theorem helper_47_AL_perp_BC :
    ∀ (a b c d l' : Point) (BC BD AL : Line),
    a.onLine AL ∧ l'.onLine AL ∧ a ≠ l' ∧
    b.onLine BC ∧ c.onLine BC ∧ l'.onLine BC ∧ b ≠ c ∧ b ≠ l' ∧
    b.onLine BD ∧ d.onLine BD ∧ b ≠ d ∧
    ¬a.onLine BC ∧ ¬d.onLine BC ∧
    ¬a.onLine BD ∧
    BC ≠ BD ∧ AL ≠ BD ∧
    (∠ c:b:d : ℝ) = ∟ ∧
    ¬AL.intersectsLine BD ∧
    a.opposingSides d BC →       -- a (apex) and d (square corner) on OPPOSITE sides of BC
    (∠ a:l':b : ℝ) = ∟ :=
by
  euclid_intros
  -- alternate angles: ∠a:l':b = ∠l':b:d  via proposition_29''' (parallels AL,BD; transversal BC)
  euclid_apply (proposition_29''' a d l' b AL BD BC)
  -- l' on BC and ∠c:b:d = ∟ ⟹ ∠l':b:d = ∟
  euclid_finish

end Elements.Book1