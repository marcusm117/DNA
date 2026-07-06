import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_c2_ang1
    (AB EF GK : Line) (a b e f g h k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (hbetw_gkh : between g k h)
    (heside : e.sameSide a GK)
    (hnopar : ¬AB.intersectsLine EF)
    : ∠ a:g:h = ∠ g:h:f := by
  have hbf : b.sameSide f GK := by euclid_finish
  euclid_apply (proposition_29'' a b f g h AB EF GK)
  assumption

end Elements.Book1
