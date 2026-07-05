import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step9
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hf_DF : f.onLine DF) (hd_DF : d.onLine DF)
    (he_DE : e.onLine DE) (hd_DE : d.onLine DE)
    (hDE_EF : DE ≠ EF) (hEF_DF : EF ≠ DF) (hDF_DE : DF ≠ DE)
    (hde : d ≠ e)
    (hang2 : ∠ b:c:a = ∠ e:f:d) :
    ∠ d:f:e = ∠ b:c:a := by
  euclid_finish

end Elements.Book1
