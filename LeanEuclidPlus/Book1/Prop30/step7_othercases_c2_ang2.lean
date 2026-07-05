import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_c2_ang2
    (EF CD GK : Line) (a c d e f g h k : Point)
    (hk_CD : k.onLine CD) (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_ehf : between e h f)
    (hbetw_ckd : between c k d)
    (hbetw_gkh : between g k h)
    (heside : e.sameSide a GK)
    (hcside : c.sameSide a GK)
    (hnopar : ¬CD.intersectsLine EF)
    : ∠ g:k:d = ∠ k:h:f := by
  have hdf : d.sameSide f GK := by euclid_finish
  euclid_apply (proposition_29' c d e f g k h CD EF GK)
  assumption

end Elements.Book1
