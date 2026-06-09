import SystemE

namespace Elements.Book1

/-
Common sub-fact for the hC11 / hC10 leaves of `helper_47_angle_dba_eq_fbc`.

TRUE (verified): `M ⊥ L` at `b`, `q` on `L`, ray `b→p` acute to `b→q` (∠p:b:q < ∟)
  ⟹ `p` on `q`'s side of the perpendicular `M`.

Proof by contradiction: if p,q opposite across M, the segment p─q meets M at some
point x; then x is on M, q is on L, and b is the L∩M foot, forcing ∠p:b:q ≥ ∟.
-/
theorem helper_47_sameSide_perp :
    ∀ (p q b r : Point) (L M : Line),
    q.onLine L ∧ b.onLine L ∧ b ≠ q ∧
    b.onLine M ∧ r.onLine M ∧ b ≠ r ∧
    L ≠ M ∧
    ¬p.onLine L ∧ ¬p.onLine M ∧
    (∠ q:b:r : ℝ) = ∟ ∧
    (∠ p:b:q : ℝ) < ∟ →
    p.sameSide q M :=
by
  euclid_intros
  by_contra hcon
  -- q is off M (q on L, q≠b, L≠M), p is off M, and they're not same-side ⟹ segment meets M.
  euclid_apply (line_from_points p q) as PQ
  euclid_apply (intersection_lines PQ M) as x
  -- x is the crossing point of segment p─q with M ⟹ x between p and q (pasch_4, sep line M)
  euclid_apply (pasch_4 p x q M PQ)
  have hbtw : between p x q := by euclid_finish
  -- x on perpendicular M (through b) and q on L ⟹ ∠q:b:x = ∟
  have hperp : (∠ q:b:x : ℝ) = ∟ := by euclid_finish
  -- ray b→x splits ∠p:b:q (x between p,q; b off line pq).  Derived, NOT via an angle axiom:
  --   pasch_2 turns the betweenness into the two sameSide facts that sum_angles_onlyif needs.
  have hsplit : (∠ p:b:q : ℝ) = (∠ p:b:x : ℝ) + (∠ x:b:q : ℝ) := by
    euclid_apply (line_from_points b p) as BP
    euclid_apply (line_from_points b q) as BQ
    euclid_apply (pasch_2 q x p BQ)   -- between q x p, q∈BQ, x∉BQ ⟹ x.sameSide p BQ
    euclid_apply (pasch_2 p x q BP)   -- between p x q, p∈BP, x∉BP ⟹ x.sameSide q BP
    euclid_apply (sum_angles_onlyif b p q x BP BQ)
    euclid_finish
  -- then ∠p:b:q = ∠p:b:x + ∟ ≥ ∟, contradicting ∠p:b:q < ∟
  euclid_finish

end Elements.Book1
