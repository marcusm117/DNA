import SystemE
import Book.Prop27
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_c3
    (AB CD GK : Line) (a b c d g h k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB)
    (hk_CD : k.onLine CD) (hd_CD : d.onLine CD)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_agb : between a g b)
    (hbetw_ckd : between c k d)
    (hnot_ghk : ¬between g h k)
    (hnot_gkh : ¬between g k h)
    (hgk : g ≠ k)
    (hstep7_othercases_c3_ang : ∠ a:g:k = ∠ g:k:d)
    (hstep7_othercases_opp : a.opposingSides d GK)
    : ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  assumption

end Elements.Book1
