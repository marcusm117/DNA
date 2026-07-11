import SystemE
import Book3.Prop02.Main
import Book3.Prop13.step4_int
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The segment db falls inside ABDC (III.2) but, since ACK(=EBFD) touches ABDC externally, outside EBFD
-- [Def.~3.3]. The "outside EBFD" reading is what makes the supposition impossible: the two distinct
-- common points d, b already force ABDC.intersectsCircle EBFD (step4_int), contradicting ¬intersect.
theorem helper_3_13_step16 (ABDC EBFD : Circle) (d b g h : Point)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hdb : d ≠ b) (hne : ABDC ≠ EBFD) (hnint : ¬ABDC.intersectsCircle EBFD)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD) :
    ∀ r : Point, between d r b → r.insideCircle ABDC ∧ r.outsideCircle EBFD := by
  have hgh : g ≠ h := by
    intro heq
    subst heq
    exact hne (by euclid_finish)
  euclid_apply (line_from_points g h) as GH
  have step4_int : ABDC.intersectsCircle EBFD := by euclid_apply (helper_3_13_step4_int ABDC EBFD d b g h GH (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle EBFD; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle EBFD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show ABDC ≠ EBFD; assumption)) (by euclid_assumption "" (show g.isCentre ABDC; assumption)) (by euclid_assumption "" (show h.isCentre EBFD; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)))
  intro r hr
  exact ⟨proposition_2 d b ABDC ⟨hd_ABDC, hb_ABDC, hdb⟩ r hr, absurd step4_int hnint⟩

end Elements.Book3
