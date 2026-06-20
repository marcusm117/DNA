import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.13 sub: ∠ l:h:g = ∟ (corner of square LHGE at H). KM ∥ AB cut by the transversal BG at feet
   h (on KM) and b (on AB); the co-interior angles ∠ g:h:l and ∠ h:b:c sum to two right angles
   (proposition_29'''''), and ∠ h:b:c = ∠ c:b:h = ∟ (step13_cbh_right). The supplement at h (between
   b h g) then gives ∠ l:h:g = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step13_lhg_right (b c g h l : Point) (AB CE BG KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG) (hgBG : g.onLine BG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hbc : b ≠ c) (hbh : b ≠ h) (hhl : h ≠ l) (hhg : h ≠ g) (hlc : l ≠ c)
    (hbhg : between b h g)
    (hcbh : ∠ c:b:h = ∟)
    (hBGCE : ¬(BG.intersectsLine CE))
    (hABKM : ¬(AB.intersectsLine KM)) :
    ∠ l:h:g = ∟ := by
  euclid_intros
  -- l.sameSide c BG: l,c both on CE ∥ BG
  have hboffCE : ¬(b.onLine CE) := by
    intro hon; euclid_apply (intersection_lines_common_point b BG CE); euclid_finish
  have hBGneCE : BG ≠ CE := fun heq => hboffCE (heq ▸ hbBG)
  have hloffBG : ¬(l.onLine BG) := by
    intro hon; euclid_apply (intersection_lines_common_point l BG CE); euclid_finish
  have hlcBG : l.sameSide c BG := by
    by_contra hns; euclid_apply (intersection_lines_opposing l c BG CE); euclid_finish
  -- co-interior: ∠ c:b:h + ∠ b:h:l = 2∟, with ∠ c:b:h = ∟ ⟹ ∠ b:h:l = ∟
  euclid_apply (proposition_29''''' c l b h AB KM BG)
  -- supplement at h: between b h g ⟹ ∠ b:h:l + ∠ l:h:g = 2∟ ⟹ ∠ l:h:g = ∟
  euclid_finish

end Elements.Book2
