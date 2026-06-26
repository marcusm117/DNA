import SystemE
import Book2.Prop01.step8_len_ss
import Book2.Prop01.step8_len_neq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.8 (length): b,d,g,k form a parallelogram with rails BC (b,d) and GH (g,k) and
   sides BF (b,g), DK (d,k). The sameSide b g DK comes from sub-node step8_len_ss; b ≠ d and k ≠ d
   come from step8_len_neq; the parallelogram is then assembled directly. -/
theorem helper_2_1_step8_len_pgram (b d e f g k : Point) (BC GH BF DK : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC) (hbde : between b d e)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hkGH : k.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF)) :
    formParallelogram b d g k BC GH BF DK := by
  euclid_intros
  have step8_len_ss : b.sameSide g DK := by euclid_apply (helper_2_1_step8_len_ss b d e f g BC BF DK (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)))
  have step8_len_neq : d ≠ k := by euclid_apply (helper_2_1_step8_len_neq d g k BC GH (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(g.onLine BC); assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)))
  refine ⟨hbBC, hdBC, hgGH, hkGH, hbBF, hgBF, ⟨hdDK, hkDK, step8_len_neq⟩, step8_len_ss, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
