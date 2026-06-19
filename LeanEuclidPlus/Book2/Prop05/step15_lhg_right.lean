import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.15 sub: ∠ l:h:g = ∟ (corner of square LEGH at H). KM ∥ AB cut by the transversal DG at feet
   h (on KM) and d (on AB); the co-interior angles ∠ g:h:l and ∠ h:d:c sum to two right angles
   (proposition_29'''''), and ∠ h:d:c = ∟ because DG ⊥ AB (DG ∥ CE, ∠ b:c:e = ∟ at the foot c).
   Concretely we are given ∠ c:d:h = ∟ (hcdh) and derive ∠ l:h:g = ∟. -/
theorem helper_2_5_step15_lhg_right (c d g h l : Point) (AB CE DG KM : Line)
    (hdAB : d.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hdc : d ≠ c) (hdh : d ≠ h) (hhl : h ≠ l) (hhg : h ≠ g) (hlc : l ≠ c)
    (hdhg : between d h g)
    (hcdh : ∠ c:d:h = ∟)
    (hDGCE : ¬(DG.intersectsLine CE))
    (hABKM : ¬(AB.intersectsLine KM)) :
    ∠ l:h:g = ∟ := by
  euclid_intros
  -- l.sameSide c DG: l,c both on CE ∥ DG
  have hdoffCE : ¬(d.onLine CE) := by
    intro hon; euclid_apply (intersection_lines_common_point d DG CE); euclid_finish
  have hDGneCE : DG ≠ CE := fun heq => hdoffCE (heq ▸ hdDG)
  have hloffDG : ¬(l.onLine DG) := by
    intro hon; euclid_apply (intersection_lines_common_point l DG CE); euclid_finish
  have hlcDG : l.sameSide c DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing l c DG CE)
    euclid_finish
  -- co-interior: ∠ c:d:h + ∠ d:h:l = 2∟, with ∠ c:d:h = ∟ ⟹ ∠ d:h:l = ∟
  euclid_apply (proposition_29''''' c l d h AB KM DG)
  -- supplement at h: between d h g ⟹ ∠ d:h:l + ∠ l:h:g = 2∟ ⟹ ∠ l:h:g = ∟
  euclid_finish

end Elements.Book2
