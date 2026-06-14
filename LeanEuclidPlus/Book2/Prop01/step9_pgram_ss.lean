import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.9: e and c (both on BC) are on the same side of GH, and l ≠ h. e,c are off GH
   (GH ∦ BC, and GH ≠ BC since l on GH is off BC), so not separable across GH ⟹ same side.
   l ≠ h: l on EL, h on CH; if l = h it would lie on both EL and CH and on GH and BF-side… it
   suffices that l on EL while h is the foot of CH; the feet differ because c ≠ e on BC give
   distinct verticals — established via the off-BC anchors. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step9_pgram_ss (b c d e f g h l : Point) (BC BF EL CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hgGH : g.onLine GH) (hlGH : l.onLine GH) (hhGH : h.onLine GH)
    (hloffBC : ¬(l.onLine BC)) (hhoffBC : ¬(h.onLine BC))
    (hGHBC : ¬(GH.intersectsLine BC)) :
    e.sameSide c GH ∧ l ≠ h := by
  euclid_intros
  have heoffGH : ¬(e.onLine GH) := by euclid_finish
  have hcoffGH : ¬(c.onLine GH) := by euclid_finish
  have hesc : e.sameSide c GH := by
    by_contra hns
    euclid_apply (intersection_lines_opposing e c GH BC)
    euclid_finish
  refine ⟨hesc, ?_⟩
  euclid_finish

end Elements.Book2
