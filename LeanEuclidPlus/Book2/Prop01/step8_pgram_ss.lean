import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.8: d and e (both on BC) are on the same side of GH, and k ≠ l. d,e are off GH
   (GH ∦ BC, GH ≠ BC since k on GH is off BC), so not separable across GH ⟹ same side. k ≠ l
   since k on DK, l on EL, and the feet differ (d ≠ e give distinct verticals). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step8_pgram_ss (b c d e f g k l : Point) (BC BF DK EL GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hlGH : l.onLine GH)
    (hkoffBC : ¬(k.onLine BC)) (hloffBC : ¬(l.onLine BC))
    (hGHBC : ¬(GH.intersectsLine BC)) :
    d.sameSide e GH ∧ k ≠ l := by
  euclid_intros
  have hdoffGH : ¬(d.onLine GH) := by euclid_finish
  have heoffGH : ¬(e.onLine GH) := by euclid_finish
  have hdse : d.sameSide e GH := by
    by_contra hns
    euclid_apply (intersection_lines_opposing d e GH BC)
    euclid_finish
  refine ⟨hdse, ?_⟩
  euclid_finish

end Elements.Book2
