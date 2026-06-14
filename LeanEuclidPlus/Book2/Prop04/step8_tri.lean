import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.8 sub: c, g, b form a triangle with sides CF (c,g), BD (g,b), AB (b,c). Pairwise line
   distinctness:
   • AB ≠ CF: g ∈ CF but g ∉ AB (g lies on HK which is parallel to AB, so g is off AB).
   • CF ≠ BD: they already share g; c ∈ CF, c ∈ AB, and if CF = BD then c ∈ BD, but c ≠ b are then
     two points of AB ∩ BD forcing AB = BD, contradicting d ∈ BD, d ∉ AB.
   • BD ≠ AB: d ∈ BD, d ∉ AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step8_tri (a b c d g : Point) (AB CF AD BD HK : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hHKAB : ¬(HK.intersectsLine AB))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟) :
    formTriangle c g b CF BD AB := by
  euclid_intros
  -- c on AB (between a, b); b ≠ c
  have step25_cab : c.onLine AB := by sorry
  have hbc : b ≠ c := by euclid_finish
  -- d ∉ AB, between b g d, then g ∉ AB (g ∈ BD, d ∈ AD∩BD, etc.)
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  euclid_finish

end Elements.Book2
