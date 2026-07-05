import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_30_step7_othercases
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
    (hgk : g ≠ k)
    (hCDneEF : CD ≠ EF)
    (hEFneAB : EF ≠ AB)
    : ¬(AB.intersectsLine CD) := by
  by_cases hc2 : between g k h
  ·
    have step7_othercases_opp : a.opposingSides d GK := by sorry
    have step7_othercases_c2_ang1 : ∠ a:g:h = ∠ g:h:f := by sorry
    have step7_othercases_c2_ang2 : ∠ g:k:d = ∠ k:h:f := by sorry
    have step7_othercases_c2_ang : ∠ a:g:k = ∠ g:k:d := by sorry
    have step7_othercases_c2 : ¬(AB.intersectsLine CD) := by sorry
    exact step7_othercases_c2
  ·
    have hkh : k ≠ h := by euclid_finish
    have hgh : g ≠ h := by euclid_finish
    have step7_othercases_opp : a.opposingSides d GK := by sorry
    have step7_othercases_c3_ang1 : ∠ d:k:h = ∠ k:h:e := by sorry
    have step7_othercases_c3_ang2 : ∠ k:g:a = ∠ g:h:e := by sorry
    have step7_othercases_c3_ang : ∠ a:g:k = ∠ g:k:d := by sorry
    have step7_othercases_c3 : ¬(AB.intersectsLine CD) := by sorry
    exact step7_othercases_c3

end Elements.Book1
