import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_pg_ekg
    (k g e f : Point) (FG EK : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (h_e_off_FG : ¬e.onLine FG)
    (hperp_k : ∠ e:k:f = ∟)
    (hkg : k ≠ g) (hke : k ≠ e)
    (h_fkg : between f k g) :
    ∠ e:k:g = ∟ := by
  euclid_finish

end Elements.Book3
