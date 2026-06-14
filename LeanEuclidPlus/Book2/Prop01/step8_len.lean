import SystemE
import Book.Prop34
import Book2.Prop01.step8_len_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.8: |d─k| = |a₁a₂|. BDKG is a parallelogram (rails BC at b,d and GH at g,k;
   sides BF at b,g and DK at d,k), so opposite sides |b─g| = |d─k| (proposition_34'); and
   |b─g| = |a₁a₂| (step2). The parallelogram is supplied as the sub-node step8_len_pgram. -/
theorem helper_2_1_step8_len (a₁ a₂ b d e f f' g k : Point) (BC GH BF DK : Line)
    (hbg : |(b─g)| = |(a₁─a₂)|)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC) (hbde : between b d e)
    (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hkGH : k.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hbBF : b.onLine BF) (hf'BF : f'.onLine BF) (hbgf' : between b g f')
    (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF)) :
    |(d─k)| = |(a₁─a₂)| := by
  euclid_intros
  euclid_apply (between_same_line_in b g f' BF)
  have step8_len_pgram : formParallelogram b d g k BC GH BF DK := by euclid_apply (helper_2_1_step8_len_pgram b d e f g k BC GH BF DK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (proposition_34' b d g k BC GH BF DK)
  euclid_finish

end Elements.Book2
