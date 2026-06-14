import SystemE
import Book2.Prop01.step8_rangle
import Book2.Prop01.step8_pgram
import Book2.Prop01.step8_len
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.8: rectangle DL (= D,E,L,K) is the rectangle contained by A and DE.
   rectangle_area on the parallelogram d,k,e,l (right angle ∠d:e:l = ∟) gives
   △d:e:l + △d:k:l = |d─k| * |d─e|. The vertical side |d─k| equals |b─g| (opposite sides of the
   parallelogram BDKG, proposition_34 — "DK, that is to say BG") which equals |a₁a₂| (step2);
   so the area is |a₁a₂| * |d─e|.
   sub-nodes: step8_rangle (∠d:e:l = ∟), step8_pgram (the DKEL parallelogram), step8_len (|d─k| = |a₁a₂|). -/
theorem helper_2_1_step8 (a₁ a₂ b c d e f f' g k l : Point) (BC BF DK EL GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbff' : between b f f') (hbgf' : between b g f')
    (hfbc : ∠ f:b:c = ∟) (hbg : |(b─g)| = |(a₁─a₂)|)
    (hgGH : g.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hkGH : k.onLine GH) (hlGH : l.onLine GH) :
    Triangle.area △ d:e:l + Triangle.area △ d:k:l = |(a₁─a₂)| * |(d─e)| := by
  euclid_intros
  have hgoffBC : ¬(g.onLine BC) := by
    euclid_apply (between_same_line_in b g f' BF)
    euclid_finish
  have hkoffBC : ¬(k.onLine BC) := by euclid_finish
  have hloffBC : ¬(l.onLine BC) := by euclid_finish
  have step8_rangle : ∠ d:e:l = ∟ := by euclid_apply (helper_2_1_step8_rangle b c d e f f' g l BC BF EL GH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_pgram : formParallelogram d k e l DK EL BC GH := by euclid_apply (helper_2_1_step8_pgram b c d e f g k l BC BF DK EL GH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_len : |(d─k)| = |(a₁─a₂)| := by euclid_apply (helper_2_1_step8_len a₁ a₂ b d e f f' g k BC GH BF DK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (rectangle_area d k e l DK EL BC GH)
  euclid_finish

end Elements.Book2
