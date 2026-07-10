import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.15 sub: ∠ c:d:h = ∟ (CD ⊥ DG at d). DG ∥ CE cut by the transversal AB at feet d (on DG... no:
   c on AB ∩ CE, d on AB ∩ DG). CE ∥ DG cut by transversal AB at feet c (on CE) and d (on DG);
   co-interior ∠ e:c:d + ∠ c:d:h = 2∟ (proposition_29'''''), and ∠ e:c:d = ∟ (= ∠ b:c:e by ray
   coincidence: between c d b ⟹ ray c→d ≡ c→b). Hence ∠ c:d:h = ∟.  e on CE, h on DG, same side of AB. -/
theorem helper_2_5_step15_cdh_right (b c d e h : Point) (AB CE DG : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hdh : d ≠ h)
    (hcdb : between c d b)
    (hbce : ∠ b:c:e = ∟)
    (hehAB : e.sameSide h AB)
    (hCEDG : ¬(CE.intersectsLine DG)) :
    ∠ c:d:h = ∟ := by
  euclid_intros
  have hcd : c ≠ d := by euclid_finish
  have hce : c ≠ e := by euclid_finish
  -- ∠ e:c:d = ∟: ray c→d ≡ c→b (between c d b), and ∠ b:c:e = ∟
  have hecd : ∠ e:c:d = ∟ := by euclid_finish
  -- co-interior on CE ∥ DG cut by AB: ∠ e:c:d + ∠ c:d:h = 2∟
  euclid_apply (proposition_29''''' e h c d CE DG AB)
  euclid_finish

end Elements.Book2
