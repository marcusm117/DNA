import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2
    (AB EF GK : Line) (a b e f g h k : Point)
    (hg_AB : g.onLine AB) (hg_GK : g.onLine GK)
    (hh_EF : h.onLine EF) (hh_GK : h.onLine GK)
    (hk_GK : k.onLine GK)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (hbetw_ghk : between g h k)
    (heside : e.sameSide a GK)
    (hnopar : ¬AB.intersectsLine EF)
    (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))
    : ∠ a:g:k = ∠ g:h:f := by
  -- b and f are on opposite sides from a and e respectively of GK, hence same side as each other
  have hbf : b.sameSide f GK := by euclid_finish
  -- alternate interior angles for AB ∥ EF with transversal GK: ∠ a:g:h = ∠ g:h:f
  euclid_apply (proposition_29'' a b f g h AB EF GK)
  -- since between g h k, the ray from g toward k passes through h: ∠ a:g:k = ∠ a:g:h
  euclid_finish

end Elements.Book1
