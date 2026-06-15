import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: f and e (both on EF) are on the same side of KM. f,e off KM (a common point of EF and KM
   would force them to meet, contra EF ∦ KM; KM ≠ EF since h ∈ KM, ¬h ∈ EF). Off KM and not separable
   ⟹ same side. (Same shape as step6_sshl with EF as the carrier line.) -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_bmf_fse (e f h : Point) (EF KM : Line)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    f.sameSide e KM := by
  euclid_intros
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  have hfoff : ¬(f.onLine KM) := by
    by_contra hfon
    euclid_apply (intersection_lines_common_point f KM EF)
    euclid_finish
  have heoff : ¬(e.onLine KM) := by
    by_contra heon
    euclid_apply (intersection_lines_common_point e KM EF)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing f e KM EF)
  euclid_finish

end Elements.Book2
