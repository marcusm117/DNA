import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: f ∉ KM. f ∈ EF, KM ∥ EF (¬KM.intersectsLine EF) and KM ≠ EF (h ∈ KM, ¬h ∈ EF). A point
   on EF cannot lie on the parallel KM. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_foffkm (f h : Point) (EF KM : Line)
    (hfEF : f.onLine EF) (hhKM : h.onLine KM)
    (hhoffEF : ¬(h.onLine EF))
    (hKMEF : ¬(KM.intersectsLine EF)) :
    ¬(f.onLine KM) := by
  intro hfKM
  have hKMneEF : KM ≠ EF := fun heq => hhoffEF (heq ▸ hhKM)
  euclid_apply (intersection_lines_common_point f KM EF)
  euclid_finish

end Elements.Book2
