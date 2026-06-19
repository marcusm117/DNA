import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

/- Shared "same side of a line" lemma — the single biggest recurring formal-gap shape in Book 2
   (the "off-then-not-separated" bucket, ~60 leaves across Prop04–07). Proved ONCE in a tiny context;
   callers collapse to one `euclid_apply (sameSide_of_parallel … (by assumption)…)`.

   Atomic hyps only (so `(by assumption)` discharges them positionally) — NO ∃-witnesses. -/

/- `p` and `q` lie on carrier `L`; a witness `w` lies on a second line `M` but off `L` (so `M ≠ L`),
   and `M` does not meet `L`. Then `p` and `q` both lie off `M` (a common point of `M` and `L` would
   make them meet), and being off `M` and not separated across it, they are on the SAME side of `M`.
   (Generalizes e.g. Prop05 step6_ssbd {p,q,w,L,M = b,d,h,AB,KM} and step6_sscl {c,l,d,CE,DG}.) -/
theorem sameSide_of_parallel (p q w : Point) (L M : Line)
    (hpL : p.onLine L) (hqL : q.onLine L)
    (hwM : w.onLine M) (hwL : ¬(w.onLine L)) (hpar : ¬(M.intersectsLine L)) :
    p.sameSide q M := by
  euclid_intros
  have hne : M ≠ L := fun h => hwL (h ▸ hwM)
  have hpoff : ¬(p.onLine M) := by
    by_contra hpon
    euclid_apply (intersection_lines_common_point p M L)
    euclid_finish
  have hqoff : ¬(q.onLine M) := by
    by_contra hqon
    euclid_apply (intersection_lines_common_point q M L)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing p q M L)
  euclid_finish

/- Sibling — witness on the CARRIER. Same "off-then-not-separated" mechanism, but the witness `u`
   that pins `L ≠ M` lies on the carrier `L` and off the target `M` (rather than on `M` off `L`), and
   the parallel is carried in the flipped orientation `¬(L.intersectsLine M)`. Covers the callers
   whose only point known-off-`M` is on `L` — including the case `u = p` (the point itself is the
   witness). (Generalizes e.g. Prop05 step6_sshg {p,q,u = h,g,d, L,M = DG,BF} and
   step6_sshl {h,l,h, KM,EF}.) -/
theorem sameSide_of_parallel' (p q u : Point) (L M : Line)
    (hpL : p.onLine L) (hqL : q.onLine L) (huL : u.onLine L)
    (huM : ¬(u.onLine M)) (hpar : ¬(L.intersectsLine M)) :
    p.sameSide q M := by
  euclid_intros
  have hne : L ≠ M := fun h => huM (h ▸ huL)
  have hpoff : ¬(p.onLine M) := by
    by_contra hpon
    euclid_apply (intersection_lines_common_point p M L)
    euclid_finish
  have hqoff : ¬(q.onLine M) := by
    by_contra hqon
    euclid_apply (intersection_lines_common_point q M L)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing p q M L)
  euclid_finish

/- Sibling — NO off-line witness, distinctness `L ≠ M` supplied directly. Both `p` and `q` lie on a
   carrier `L` that does not meet `M` (`¬(L.intersectsLine M)`) and `L ≠ M`. The parallel + distinctness
   force both points off `M` (a point on `L ∩ M` with `L ≠ M` would make them meet), so no separate
   off-`M` witness is needed. The `L ≠ M` hypothesis is ESSENTIAL: without it `L = M` is a countermodel
   (`p,q ∈ L = M`, `¬intersects` vacuous), so the parallel alone does NOT force them off `M`. This is the
   simplest rectangle shape once `L ≠ M` is in hand — "two corners on one side line are same-side w.r.t.
   the opposite side line." (Generalizes e.g. Prop05 step8_cmpar_flip_lss {p,q,L,M = l,c,CE,BF}.) -/
theorem sameSide_of_parallel_both (p q : Point) (L M : Line)
    (hpL : p.onLine L) (hqL : q.onLine L) (hne : L ≠ M) (hpar : ¬(L.intersectsLine M)) :
    p.sameSide q M := by
  euclid_intros
  have hpoff : ¬(p.onLine M) := by
    intro hon
    exact hpar (by euclid_apply (intersection_lines_common_point p L M); euclid_finish)
  have hqoff : ¬(q.onLine M) := by
    intro hon
    exact hpar (by euclid_apply (intersection_lines_common_point q L M); euclid_finish)
  by_contra hns
  euclid_apply (intersection_lines_opposing p q M L)
  euclid_finish

end Elements
