import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.9: |(c─b)| = |(g─k)|. CGKB is a parallelogram (c,b on AB; g,k on HK ∥ AB; c,g on CF; b,k on
   BE ∥ CF), so opposite sides c─b and g─k are equal [Prop.~1.34]. The parallelogram itself is the
   shared sub-node step9_par (which needs the root off-line facts c∉AD, a∉BE, d∉AB and b≠g, derived
   here); proposition_34' then yields |c─b| = |g─k|. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step9 (a b c d e g k : Point) (AB CF AD BE HK BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    |(c─b)| = |(g─k)| := by
  euclid_intros
  -- root off-line facts and the interior distinctness b ≠ g
  have had : a ≠ d := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  -- b ≠ d: b ∈ AB but d ∉ AB
  have hbd : b ≠ d := fun h => step8_dnab (h ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_par : formParallelogram c b g k AB HK CF BE := by sorry
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
