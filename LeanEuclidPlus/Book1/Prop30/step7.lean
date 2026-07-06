import SystemE
import Book1.Prop27.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7
    (AB CD GK : Line) (a d g k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB)
    (hk_CD : k.onLine CD) (hd_CD : d.onLine CD)
    (hg_GK : g.onLine GK) (hk_GK : k.onLine GK)
    (hga : g ≠ a)
    (hbetw_ckd : between c k d)
    (hbetw_ghk : between g h k)
    (hstep5 : ∠ a:g:k = ∠ g:k:d)
    (hstep6 : a.opposingSides d GK)
    : ¬(AB.intersectsLine CD) := by
  euclid_apply (proposition_27 a d g k AB CD GK)
  assumption

end Elements.Book1
