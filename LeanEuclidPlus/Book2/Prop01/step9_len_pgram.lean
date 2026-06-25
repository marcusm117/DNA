import SystemE
import Book2.Prop01.step9_len_ss
import Book2.Prop01.step9_len_neq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.9 (length): b,e,g,l form a parallelogram with rails BC (b,e) and GH (g,l) and
   sides BF (b,g), EL (e,l). The sameSide b g EL and e ≠ l facts come from the sub-node
   step9_len_ss; the parallelogram is then assembled directly from the incidences. -/
theorem helper_2_1_step9_len_pgram (b d e f g l : Point) (BC GH BF EL : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC) (hbde : between b d e)
    (hbBF : b.onLine BF) (hgBF : g.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hgGH : g.onLine GH) (hgoffBC : ¬(g.onLine BC)) (hlGH : l.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF)) :
    formParallelogram b e g l BC GH BF EL := by
  euclid_intros
  have step9_len_ss : b.sameSide g EL := by euclid_apply (helper_2_1_step9_len_ss b d e f g BC BF EL (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_len_neq : e ≠ l := by euclid_apply (helper_2_1_step9_len_neq e g l BC GH (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  refine ⟨hbBC, heBC, hgGH, hlGH, hbBF, hgBF, ⟨heEL, hlEL, step9_len_neq⟩, step9_len_ss, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
