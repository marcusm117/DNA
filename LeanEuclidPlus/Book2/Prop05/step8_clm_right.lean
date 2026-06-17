import SystemE
import Book.Prop29
import Book2.Helpers.RightAngle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8 sub: ∠ c:l:m = ∟ (rectangle CM has a right angle at l = KM ∩ CE).
   KM ∥ AB are cut by the transversal CE at the feet l (on KM) and c (on AB).
   The co-interior angles sum to two right angles (proposition_29'''''):
     ∠ m:l:c + ∠ l:c:b = ∟ + ∟.
   And ∠ l:c:b = ∟ by ray-rewrite: l lies on ray c→e (between c l e), so
   ∠ l:c:b = ∠ e:c:b = ∟ (given ∠ b:c:e = ∟). Hence ∠ c:l:m = ∟ (= ∠ m:l:c).
   m.sameSide b CE: m on BF ∥ CE so m.sameSide f CE-side; b on AB. Built by transitivity
   through the figure; off-CE facts are Main-supplied. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_clm_right (b c e l m f : Point) (AB CE KM BF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hbBF : b.onLine BF) (hmBF : m.onLine BF) (hfBF : f.onLine BF)
    (hcle : between c l e)
    (hbce : ∠ b:c:e = ∟)
    (hbmf : between b m f)
    (hmoffCE : ¬(m.onLine CE)) (hboffCE : ¬(b.onLine CE))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) :
    ∠ c:l:m = ∟ := by
  euclid_intros
  -- ray-rewrite: l on ray c→e ⟹ ∠ l:c:b = ∠ e:c:b = ∟
  have hlcb : ∠ l:c:b = ∟ := by euclid_finish
  -- m.sameSide b CE by transitivity: m on BF ∥ CE links to b via the figure
  have hmb : m.sameSide b CE := by
    by_contra hns
    euclid_apply (intersection_lines_opposing m b CE BF)
    euclid_finish
  -- co-interior core via the shared lemma: KM ∥ AB cut by CE at feet l,c; ∠l:c:b = ∟ ⟹ ∠m:l:c = ∟
  euclid_apply (right_angle_cointerior m b l c KM AB CE)
  euclid_finish

end Elements.Book2
