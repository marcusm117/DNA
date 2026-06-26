import SystemE
import Book2.Prop01.step9_pgram_par
import Book2.Prop01.step9_pgram_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.9: e,l,c,h form a parallelogram with sides EL (e,l), CH (c,h), rail BC (e,c)
   and rail GH (l,h). The two non-incidence facts are supplied by sub-nodes: step9_pgram_par
   (EL ∦ CH, via proposition_30) and step9_pgram_ss (e.sameSide c GH and l ≠ h). The assembly is
   then a direct ⟨…⟩ (the BC ∦ GH conjunct is an orientation flip of the given). -/
theorem helper_2_1_step9_pgram (b c d e f g h l : Point) (BC BF EL CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hgGH : g.onLine GH) (hlGH : l.onLine GH) (hhGH : h.onLine GH)
    (hloffBC : ¬(l.onLine BC)) (hhoffBC : ¬(h.onLine BC))
    (hGHBC : ¬(GH.intersectsLine BC)) :
    formParallelogram e l c h EL CH BC GH := by
  euclid_intros
  have step9_pgram_par : ¬(EL.intersectsLine CH) := by euclid_apply (helper_2_1_step9_pgram_par b c d e f h l BC BF EL CH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(l.onLine BC); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬(h.onLine BC); assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)))
  have step9_pgram_ss : e.sameSide c GH ∧ l ≠ h := by euclid_apply (helper_2_1_step9_pgram_ss b c d e f g h l BC BF EL CH GH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show ¬(l.onLine BC); assumption)) (by euclid_assumption "" (show ¬(h.onLine BC); assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)))
  obtain ⟨hesc, hlh⟩ := step9_pgram_ss
  refine ⟨heEL, hlEL, hcCH, hhCH, heBC, hcBC, ⟨hlGH, hhGH, hlh⟩, hesc, step9_pgram_par, ?_⟩
  euclid_finish

end Elements.Book2
