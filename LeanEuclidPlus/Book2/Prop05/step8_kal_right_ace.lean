import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub-sub: ∠ a:c:e = ∟. CE ⊥ AB at c: ∠ b:c:e = ∟, and a,c,b are collinear with
   c between a and b (between a c d, between c d b ⟹ a–c–b straight), so the angle on the
   other ray ∠ a:c:e is the supplement of the right angle ∠ b:c:e, hence also right. -/
theorem helper_2_5_step8_kal_right_ace (a b c d e : Point) (AB CE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hacd : between a c d) (hcdb : between c d b)
    (hbce : ∠ b:c:e = ∟) :
    ∠ a:c:e = ∟ := by
  euclid_intros
  euclid_finish

end Elements.Book2
