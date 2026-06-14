import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.32: ADEB is the square on AB — area(ADEB) = |a─b|². ADEB is a parallelogram (step25_bigpar);
   rectangle_area with the right angle ∠ b:a:d = ∟ gives area = |a─b|² in the b:a:d / b:e:d
   triangulation (step32_rect), and parallelogram_area bridges to our a:d:e / a:e:b triangulation
   (step32_bridge). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step32 (a b d e : Point) (BE AD AB DE : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (heDE : e.onLine DE) (hdDE : d.onLine DE)
    (hADBE : ¬(AD.intersectsLine BE)) (hDEAB : ¬(DE.intersectsLine AB))
    (hab : a ≠ b) (hbe : |(b─e)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hade : ∠ a:d:e = ∟) :
    Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)| := by
  euclid_intros
  -- ADEB parallelogram preamble
  have had : a ≠ d := by euclid_finish
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have hABDE : AB ≠ DE := fun hh => step8_dnab (hh ▸ hdDE)
  have step25_bead : ¬(BE.intersectsLine AD) := by sorry
  have step25_abde : ¬(AB.intersectsLine DE) := by sorry
  have hed2 : e ≠ d := by euclid_finish
  have step25_bchk2 : b.sameSide a DE := by sorry
  have step25_bigpar : formParallelogram b e a d BE AD AB DE := by sorry
  -- the rectangle area (one triangulation) and the bridge to ours
  have step32_rect : Triangle.area △ b:a:d + Triangle.area △ b:e:d = |(a─b)| * |(a─b)| := by sorry
  have step32_bridge : Triangle.area △ a:d:e + Triangle.area △ a:e:b
      = Triangle.area △ b:a:d + Triangle.area △ b:e:d := by sorry
  rw [step32_bridge, step32_rect]

end Elements.Book2
