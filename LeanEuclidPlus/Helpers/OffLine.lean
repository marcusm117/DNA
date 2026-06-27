import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

/- Shared "point off a line" lemmas — the formal-gap glue Euclid leaves implicit. Each is the
   generalized body of a recurring Book-2 leaf, proved ONCE in a tiny context so its SMT query is
   small and lands fast; callers collapse to a one-line `euclid_apply (… (by assumption)…)`.

   Hypotheses are ATOMIC facts (`p.onLine L`, `¬(p.onLine L)`, `p ≠ q`, `∠…=∟`,
   `¬(L.intersectsLine M)`) so the pipeline can discharge them positionally with `(by assumption)`.
   NO ∃-witness hypotheses — `by assumption` cannot synthesize an existential. -/

/- Mechanism A — angle-degeneracy. Vertex `a` and a second point `b` lie on `L`; the ray `a→d`
   makes a right angle with `a→b`. If `d` were on `L` too, `b,a,d` would be collinear and the right
   angle ∠b:a:d would be a degenerate straight/zero angle — impossible.
   (Generalizes e.g. Prop04 step8_dnab / step9_anbe.) -/
theorem offLine_of_right_angle (a b d : Point) (L : Line)
    (haL : a.onLine L) (hbL : b.onLine L) (hab : a ≠ b) (had : a ≠ d)
    (hang : ∠ b:a:d = ∟) : ¬(d.onLine L) := by
  intro hdL
  euclid_finish

/- Mechanism B — two-points-determine-line. `x` and `c` are DISTINCT points on `L`; `c` also lies on
   `M`, and a witness `w` lies on `M` but off `L`. If `x` were on `M`, then `x,c` would be two
   distinct common points of `L` and `M`, forcing `L = M` and hence `w ∈ L` — contradiction.
   (Generalizes e.g. Prop05 step6_doffce, Prop04 step26_bnad.) -/
theorem offLine_of_two_points (x c w : Point) (L M : Line)
    (hxL : x.onLine L) (hcL : c.onLine L) (hxc : x ≠ c)
    (hcM : c.onLine M) (hwM : w.onLine M) (hwL : ¬(w.onLine L)) : ¬(x.onLine M) := by
  intro hxM
  have hLM : L = M := by
    euclid_apply (two_points_determine_line x c L M)
    euclid_finish
  exact hwL (hLM ▸ hwM)

/- Mechanism B′ — two-points-determine-line, witness on the CARRIER. Same as B, but the witness `w`
   that distinguishes `L` from `M` lies on `L` (off `M`) rather than on `M` (off `L`). `x` and `c`
   are distinct on `L`; `c` also on `M`. If `x ∈ M`, then `x,c` are two common points ⟹ `L = M` ⟹
   `w ∈ M` (from `w ∈ L`), contradicting `¬(w.onLine M)`.
   (Generalizes e.g. Prop05 step6_hoffef and step6_bmf_hoffab, whose witness `b`/`e` lies on the
   shared line `BE` off the target.) -/
theorem offLine_of_two_points' (x c w : Point) (L M : Line)
    (hxL : x.onLine L) (hcL : c.onLine L) (hxc : x ≠ c)
    (hcM : c.onLine M) (hwL : w.onLine L) (hwM : ¬(w.onLine M)) : ¬(x.onLine M) := by
  intro hxM
  have hLM : L = M := by
    euclid_apply (two_points_determine_line x c L M)
    euclid_finish
  exact hwM (hLM ▸ hwL)

/- Mechanism C — parallel / intersection-common-point. `x` lies on carrier `L`; a witness `w` lies
   on `M` but off `L` (so `M ≠ L`); and `M` does not meet `L`. If `x` were on `M`, it would be a
   common point of `M` and `L`, contradicting `¬(M.intersectsLine L)`.
   (Generalizes e.g. Prop04 step15_ande / step15_bnhk.) -/
theorem offLine_of_parallel (x w : Point) (L M : Line)
    (hxL : x.onLine L) (hwM : w.onLine M) (hwL : ¬(w.onLine L))
    (hpar : ¬(M.intersectsLine L)) : ¬(x.onLine M) := by
  intro hxM
  have hne : M ≠ L := fun h => hwL (h ▸ hwM)
  euclid_apply (intersection_lines_common_point x M L)
  euclid_finish

/- Mechanism C₀ — NO off-line witness, but the carrier/target distinctness `L ≠ M` is supplied
   directly. `x` lies on a carrier `L` that does not meet `M` (`¬(L.intersectsLine M)`) and `L ≠ M`;
   then `x` is off `M` (a common point of two DISTINCT non-meeting lines is impossible). The `L ≠ M`
   hypothesis is ESSENTIAL: without it `L = M` is a countermodel (`x ∈ L = M` while `¬intersects`
   holds vacuously), so the parallel alone does NOT force `x` off `M`. Use when `L ≠ M` is already a
   named fact in context but no off-`M` witness point is. (Generalizes e.g. Prop05 step8_moffce.) -/
theorem offLine_of_parallel_simple (x : Point) (L M : Line)
    (hxL : x.onLine L) (hne : L ≠ M) (hpar : ¬(L.intersectsLine M)) : ¬(x.onLine M) := by
  intro hxM
  exact hpar (by euclid_apply (intersection_lines_common_point x L M); euclid_finish)

/- Mechanism C₀′ — C₀ with the parallel in the OTHER orientation (`¬(M.intersectsLine L)`).
   `intersectsLine` is not definitionally symmetric, so a caller holding the flipped non-intersection
   needs this sibling. `L ≠ M` is required for the same reason as C₀. (Generalizes e.g. Prop05
   step11_eoffDG / step8_moffce.) -/
theorem offLine_of_parallel_simple' (x : Point) (L M : Line)
    (hxL : x.onLine L) (hne : L ≠ M) (hpar : ¬(M.intersectsLine L)) : ¬(x.onLine M) := by
  intro hxM
  exact hpar (by euclid_apply (intersection_lines_common_point x M L); euclid_finish)

/- Mechanism C′ — same as C but with the parallel hypothesis in the OTHER orientation
   (`¬(L.intersectsLine M)`), which is the form callers carry when the parallel was DERIVED
   (e.g. via proposition_30) rather than taken from the proposition's givens. The `(by assumption)`
   wire is exact up to defeq and `intersectsLine` symmetry is NOT definitional, so a caller with the
   flipped orientation needs this sibling. (Generalizes e.g. Prop05 step6_doffbf / step6_hoffbf,
   which carry the derived `¬(DG.intersectsLine BF)`.) -/
theorem offLine_of_parallel' (x w : Point) (L M : Line)
    (hxL : x.onLine L) (hwM : w.onLine M) (hwL : ¬(w.onLine L))
    (hpar : ¬(L.intersectsLine M)) : ¬(x.onLine M) := by
  intro hxM
  have hne : M ≠ L := fun h => hwL (h ▸ hwM)
  euclid_apply (intersection_lines_common_point x M L)
  euclid_finish

/- Line-distinctness from an off-line anchor — the ubiquitous `fun h => hpM (h ▸ hpL)` term written
   inline ~60× across Prop04–09 (and the precondition feedstock for `not_intersects_trans`'s three
   line-≠ args and the no-witness off-line / sameSide siblings, which REQUIRE an explicit `L ≠ M`).
   `p` lies on `L` but off `M`, so `L = M` would put `p` on `M` — impossible. Pure term, zero SMT.
   For the flipped `M ≠ L`, use `(line_ne_of_offLine p L M hpL hpM).symm`. -/
theorem line_ne_of_offLine (p : Point) (L M : Line)
    (hpL : p.onLine L) (hpM : ¬(p.onLine M)) : L ≠ M :=
  fun h => hpM (h ▸ hpL)

end Elements
