import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_step7
    (a b c d e f g h : Point) (AB CD EF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hcd : c ≠ d)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hef : e ≠ f)
    (hbetw_agb : between a g b) (hbetw_chd : between c h d)
    (hbetw_egh : between e g h) (hbetw_ghf : between g h f)
    (hside : b.sameSide d EF)
    (hlt : ∠ b:g:h + ∠ g:h:d < ∟ + ∟) :
    ∠ b:g:h + ∠ g:h:d < ∟ + ∟ → AB.intersectsLine CD := by
  intro _
  euclid_finish

end Elements.Book1
