import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: ¬(e.onLine KM). e ∈ EF; KM ∥ EF (hKMEF). KM ≠ EF because h ∈ KM is off EF
   (step8_hoffef). A common point e would then force KM, EF to meet. -/
theorem helper_2_5_step8_eoffkm (e h : Point) (EF KM : Line)
    (heEF : e.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    ¬(e.onLine KM) := by
  intro heKM
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  euclid_apply (intersection_lines_common_point e KM EF)
  euclid_finish

end Elements.Book2
