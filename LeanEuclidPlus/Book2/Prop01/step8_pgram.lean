import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.8: d,k,e,l form a parallelogram with sides DK (d,k), EL (e,l), rail BC (d,e)
   and rail GH (k,l). DK ∦ EL (sub-node step8_pgram_par, via proposition_30 since both ∦ BF).
   The sameSide d e GH (both on BC ∥ GH) and k ≠ l come from step8_pgram_ss; the parallelogram
   is then assembled directly (the BC ∦ GH conjunct is an orientation flip of the given). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step8_pgram (b c d e f g k l : Point) (BC BF DK EL GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hlGH : l.onLine GH)
    (hkoffBC : ¬(k.onLine BC)) (hloffBC : ¬(l.onLine BC))
    (hGHBC : ¬(GH.intersectsLine BC)) :
    formParallelogram d k e l DK EL BC GH := by
  euclid_intros
  have step8_pgram_par : ¬(DK.intersectsLine EL) := by sorry
  have step8_pgram_ss : d.sameSide e GH ∧ k ≠ l := by sorry
  obtain ⟨hdse, hkl⟩ := step8_pgram_ss
  refine ⟨hdDK, hkDK, heEL, hlEL, hdBC, heBC, ⟨hkGH, hlGH, hkl⟩, hdse, step8_pgram_par, ?_⟩
  euclid_finish

end Elements.Book2
