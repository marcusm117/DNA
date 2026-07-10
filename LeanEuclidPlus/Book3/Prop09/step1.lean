import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_9_step1
    (a b c e f : Point) (AB BC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC) (hbc : b ≠ c)
    (haeb : between a e b) (haeb_eq : |(a─e)| = |(e─b)|)
    (hbfc : between b f c) (hbfc_eq : |(b─f)| = |(f─c)|) :
    distinctPointsOnLine a b AB ∧ distinctPointsOnLine b c BC ∧
    between a e b ∧ |(a─e)| = |(e─b)| ∧ between b f c ∧ |(b─f)| = |(f─c)| :=
  ⟨⟨ha_AB, hb_AB, hab⟩, ⟨hb_BC, hc_BC, hbc⟩, haeb, haeb_eq, hbfc, hbfc_eq⟩

end Elements.Book3
