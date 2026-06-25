import SystemE
import Book2.Prop01.step6_rangle
import Book2.Prop01.step6_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.6: rectangle BH (= B,C,H,G) is the rectangle contained by A and BC.
   BH is contained by GB and BC (rectangle_area on the parallelogram b,g,c,h with the right angle
   ∠b:c:h = ∟), giving area = |b─g| * |b─c|; and |b─g| = |a₁a₂| (step2), so area = |a₁a₂| * |b─c|.
   The right angle at c (step6_rangle) and the parallelogram (step6_pgram) are derived as sub-nodes. -/
theorem helper_2_1_step6 (a₁ a₂ b c f f' g h : Point) (BC BF CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hbc : b ≠ c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbff' : between b f f') (hbgf' : between b g f')
    (hfbc : ∠ f:b:c = ∟) (hbg : |(b─g)| = |(a₁─a₂)|)
    (hgGH : g.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hhGH : h.onLine GH) :
    Triangle.area △ b:c:h + Triangle.area △ b:g:h = |(a₁─a₂)| * |(b─c)| := by
  euclid_intros
  have step6_rangle : ∠ b:c:h = ∟ := by euclid_apply (helper_2_1_step6_rangle b c f f' g h BC BF CH GH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step6_pgram : formParallelogram b g c h BF CH BC GH := by euclid_apply (helper_2_1_step6_pgram b c f f' g h BC BF CH GH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_apply (rectangle_area b g c h BF CH BC GH)
  euclid_finish

end Elements.Book2
