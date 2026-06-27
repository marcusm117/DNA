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

end Elements
