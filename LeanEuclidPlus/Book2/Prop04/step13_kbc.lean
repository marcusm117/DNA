import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.15: ∠ k:b:c = ∟. At the square corner b, ∠ a:b:e = ∟. The ray b→c coincides with b→a
   (c between a, b on AB) and the ray b→k coincides with b→e (k between b, e on BE — step15_bke),
   so ∠ k:b:c = ∠ e:b:a = ∟ (equal_angles + angle symmetry). -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step13_kbc (a b c d e g k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hkBE : k.onLine BE)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (heb : e ≠ b)
    (hab : a ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    ∠ k:b:c = ∟ := by
  euclid_intros
  -- off-line roots and interior distinctness needed by step15_bke
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  have hbd : b ≠ d := fun h => step8_dnab (h ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  -- k between b and e on the right side
  have step15_bke : between b k e := by sorry
  have hkb : k ≠ b := ((between_symm b k e step15_bke).2.1).symm
  euclid_apply (equal_angles b k e c a BE AB)
  euclid_finish

end Elements.Book2
