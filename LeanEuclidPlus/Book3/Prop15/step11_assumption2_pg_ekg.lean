import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step11_assumption2_pg_ekg
    (k g e f : Point) (FG : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (hperp_k : ∠ e:k:f = ∟) :
    ∠ e:k:g = ∟ := by
  euclid_finish

end Elements.Book3
