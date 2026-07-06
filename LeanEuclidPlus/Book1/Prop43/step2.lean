import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step2
    (a e k h : Point) (AD EF AB GH AC : Line)
    (h_a_AD : a.onLine AD) (h_h_AD : h.onLine AD)
    (h_e_EF : e.onLine EF) (h_k_EF : k.onLine EF)
    (h_a_AB : a.onLine AB) (h_e_AB : e.onLine AB)
    (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH)
    (h_hk : h ≠ k)
    (h_sameSide : a.sameSide e GH)
    (h_par_AD_EF : ¬AD.intersectsLine EF)
    (h_par_AB_GH : ¬AB.intersectsLine GH)
    (hassump1 : formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC)
    : Triangle.area △ a:e:k = Triangle.area △ a:h:k := by
  euclid_apply (proposition_34 h a k e AD EF GH AB AC)
  euclid_finish

end Elements.Book1
