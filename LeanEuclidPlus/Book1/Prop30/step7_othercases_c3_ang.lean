import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_c3_ang
    (AB CD EF GK : Line) (a b c d e f g h k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hk_CD : k.onLine CD) (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (hbetw_ckd : between c k d)
    (heside : e.sameSide a GK)
    (hcside : c.sameSide a GK)
    (hnopar_AB : ¬AB.intersectsLine EF)
    (hnopar_CD : ¬CD.intersectsLine EF)
    (hnot_ghk : ¬between g h k)
    (hnot_gkh : ¬between g k h)
    (hgk : g ≠ k)
    (hkh : k ≠ h)
    (hgh : g ≠ h)
    (hc3_ang1 : ∠ d:k:h = ∠ k:h:e)
    (hc3_ang2 : ∠ k:g:a = ∠ g:h:e)
    : ∠ a:g:k = ∠ g:k:d := by
  euclid_finish

end Elements.Book1
