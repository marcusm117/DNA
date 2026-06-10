import SystemE

namespace Elements.Book2

-- between b g d : G = CF∩BD lies between B and D on the diagonal.
-- CF (vertical through C) separates B from D: C between A,B puts B and A on opposite sides of CF;
-- A and D are on the same side (AD ∥ CF, doesn't cross it). So B,D opposite across CF; G=CF∩BD
-- between them by pasch_4.
set_option systemE.solverTime 30 in
theorem helper_2_pos_bgd (a b c d g : Point) (AB AD CF BD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hacb : between a c b)
    (hab : a ≠ b)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hgBD : g.onLine BD)
    (hgCF : g.onLine CF) (hbd : b ≠ d) (hbg : b ≠ g) (hdg : d ≠ g)
    (hCFBD : CF ≠ BD) :
    between b g d := by
  euclid_intros
  -- A and D on the same side of CF (AD ∥ CF); A and B on opposite sides (C between them on AB)
  euclid_apply (pasch_4 b g d CF BD)
  euclid_finish

end Elements.Book2
