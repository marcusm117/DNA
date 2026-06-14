import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.7: rectangle BK (= B,D,K,G) is the rectangle contained by A and BD.
   BK is contained by GB and BD (rectangle_area on the parallelogram b,g,d,k with the right angle
   ∠b:d:k = ∟), giving area = |b─g| * |b─d|; and |b─g| = |a₁a₂| (step2), so area = |a₁a₂| * |b─d|.
   The right angle at d (step7_rangle) and the parallelogram (step7_pgram) are derived as sub-nodes. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step7 (a₁ a₂ b c d e f f' g k : Point) (BC BF DK GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbff' : between b f f') (hbgf' : between b g f')
    (hfbc : ∠ f:b:c = ∟) (hbg : |(b─g)| = |(a₁─a₂)|)
    (hgGH : g.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (hkGH : k.onLine GH) :
    Triangle.area △ b:d:k + Triangle.area △ b:g:k = |(a₁─a₂)| * |(b─d)| := by
  euclid_intros
  have step7_rangle : ∠ b:d:k = ∟ := by sorry
  have step7_pgram : formParallelogram b g d k BF DK BC GH := by sorry
  euclid_apply (rectangle_area b g d k BF DK BC GH)
  euclid_finish

end Elements.Book2
