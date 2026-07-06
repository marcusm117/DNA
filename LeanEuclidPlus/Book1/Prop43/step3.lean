import SystemE
import Book1.Prop34.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step3
    (k f g c : Point) (EF BC GH CD AC : Line)
    (h_k_EF : k.onLine EF) (h_f_EF : f.onLine EF)
    (h_g_BC : g.onLine BC) (h_c_BC : c.onLine BC)
    (h_k_GH : k.onLine GH) (h_g_GH : g.onLine GH)
    (h_f_CD : f.onLine CD) (h_c_CD : c.onLine CD)
    (h_fc : f ≠ c)
    (h_sameSide : k.sameSide g CD)
    (h_par_EF_BC : ¬EF.intersectsLine BC)
    (h_par_GH_CD : ¬GH.intersectsLine CD)
    (h_k_AC : k.onLine AC) (h_c_AC : c.onLine AC)
    : Triangle.area △ k:f:c = Triangle.area △ k:g:c := by
  euclid_apply (proposition_34 f k c g EF BC CD GH AC)
  euclid_finish

end Elements.Book1
