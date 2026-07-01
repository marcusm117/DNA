import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements

open Elements.Book1

/- Corresponding angles at the two feet of a transversal cutting two parallels — the recurring
   "diagonal cuts the two parallel sides" angle-equality that shows up across the II.5/II.6/II.7
   isosceles arguments (Prop05 step13_dhdb_corr, Prop06 step11_dmdb_corr, Prop07 step9_corr).

   `L1 ∥ L2` (¬(L1.intersectsLine L2)); the transversal `T` runs through `b`, the near foot `h`
   (on L1), and the far foot `e` (on L2), with `h` between `b` and `e`; `d` (on L1) and `c` (on L2)
   are on the same side of `T`. proposition_29'''' gives the corresponding angle `∠ b:h:d = ∠ h:e:c`;
   the ray e→h coincides with e→b (h between b,e) so `∠ c:e:h = ∠ c:e:b`, and the angle symmetries
   close `∠ d:h:b = ∠ c:e:b`. (Verbatim generalization of the proven Prop05 leaf.)

   Atomic hyps only (onLine / between / sameSide / ¬intersectsLine) so callers discharge by
   `assumption`. The conclusion orientation here is Prop05's; Prop06/07 cut the SAME figure but
   name the far transversal endpoint differently — PROMOTE an orientation sibling here when you hit
   one (the body is identical modulo which endpoint the rays close to), exactly as OffLine/SameSide
   carry siblings. -/
theorem corresponding_angle (b c d e h : Point) (L1 L2 T : Line)
    (hdL1 : d.onLine L1) (hhL1 : h.onLine L1)
    (hcL2 : c.onLine L2) (heL2 : e.onLine L2)
    (hbT : b.onLine T) (hhT : h.onLine T) (heT : e.onLine T)
    (hbhe : between b h e) (hdcT : d.sameSide c T)
    (hpar : ¬(L1.intersectsLine L2)) :
    ∠ d:h:b = ∠ c:e:b := by
  euclid_intros
  -- corresponding angles via proposition_29'''': ∠ b:h:d = ∠ h:e:c
  have hcorr : ∠ b:h:d = ∠ h:e:c := by
    euclid_apply (proposition_29'''' d c b h e L1 L2 T)
    euclid_finish
  -- ray e→h coincides with e→b (h between b and e), so ∠ c:e:h = ∠ c:e:b
  have hray : ∠ c:e:h = ∠ c:e:b := by
    euclid_apply (equal_angles e h b c c T L2)
    euclid_finish
  -- symmetries (∠ d:h:b = ∠ b:h:d, ∠ h:e:c = ∠ c:e:h) close the chain
  euclid_finish

/- Angle split by an interior ray — the curried `sum_angles_onlyif` axiom. Vertex `a`, ray `a→b` on
   `L`, ray `a→c` on `M`, and an interior direction `d` off both `L` and `M` with `b`,`c` each on the
   `d`-side of the OTHER ray's line; then the whole angle `∠ b:a:c` splits as `∠ b:a:d + ∠ d:a:c`.

   The recurring Book-1 angle-arithmetic shape (~13 sites across Prop05/07/14/20/24…): the FLAT proofs
   call the axiom bare and let `euclid_apply` discharge the `sameSide` preconditions via SMT — this
   wrapper takes them as ATOMIC hyps so a faithful-pipeline caller discharges by `assumption` with ZERO
   SMT (the OffLine/SameSide/Pasch pattern). Its converse `sum_angles_if` (angle-sum ⟹ the two sameSide
   facts, Prop18) is the natural sibling — PROMOTE it here when a caller needs that direction. -/
theorem angle_split (a b c d : Point) (L M : Line)
    (haL : a.onLine L) (haM : a.onLine M) (hbL : b.onLine L) (hcM : c.onLine M)
    (hab : a ≠ b) (hac : a ≠ c) (hdL : ¬(d.onLine L)) (hdM : ¬(d.onLine M))
    (hLM : L ≠ M) (hbd : b.sameSide d M) (hcd : c.sameSide d L) :
    ∠ b:a:c = ∠ b:a:d + ∠ d:a:c := by
  euclid_apply (sum_angles_onlyif a b c d L M)
  euclid_finish

end Elements
