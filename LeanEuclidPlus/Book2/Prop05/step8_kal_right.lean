import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8 sub: ∠ k:a:c = ∟ (rectangle AL has a right angle at a).
   AK ∥ CE are cut by the transversal AB at the feet a (on AK) and c (on CE).
   The co-interior angles sum to two right angles (proposition_29'''''):
     ∠ k:a:c + ∠ a:c:e = ∟ + ∟.
   And ∠ a:c:e = ∟ since CE ⊥ AB at c: ∠ b:c:e = ∟ and a–c–b is straight
   (between a c d, between c d b ⟹ a,c,b collinear with c between), so the
   supplement ∠ a:c:e is also right. Hence ∠ k:a:c = ∟.
   k.sameSide e AB: k is on KM ∥ AB, e is on EF ∥ AB, both above AB (l on KM∩CE links them). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_kal_right (a b c d e k l : Point) (AB AK CE KM EF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM)
    (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b)
    (hbce : ∠ b:c:e = ∟)
    (hAKCE : ¬(AK.intersectsLine CE))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    ∠ k:a:c = ∟ := by
  euclid_intros

  have h1 : CE.intersectsLine AB := by
   sorry
  
  -- have step8_kal_right_ace : ∠ a:c:e = ∟ := by sorry
  -- have step8_kal_right_kse : k.sameSide e AB := by sorry
  -- euclid_apply (Elements.Book1.proposition_29''''' k e a c AK CE AB)
  -- euclid_finish

end Elements.Book2
