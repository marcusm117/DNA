import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_8_step24_oeh (a e f h o : Point) (AE EF : Line)
    (h_a_ae : a.onLine AE) (h_e_ae : e.onLine AE) (h_o_ae : o.onLine AE)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF) (h_h_ef : h.onLine EF)
    (h_aef : ∠ a:e:f = ∟)
    (h_aoe : between a o e) (h_ehf : between e h f) :
    ∠ o:e:h = ∟ := by
  euclid_finish

end Elements.Book2
