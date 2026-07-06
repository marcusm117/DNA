import SystemE
import Book1Variants.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_c3_ang2
    (AB EF GK : Line) (a b e f g h k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (heside : e.sameSide a GK)
    (hnopar : ¬AB.intersectsLine EF)
    (hnot_ghk : ¬between g h k)
    (hnot_gkh : ¬between g k h)
    (hgk : g ≠ k)
    (hkh : k ≠ h)
    (hgh : g ≠ h)
    : ∠ k:g:a = ∠ g:h:e := by
  euclid_apply (proposition_29' b a f e k g h AB EF GK)
  assumption

end Elements.Book1
