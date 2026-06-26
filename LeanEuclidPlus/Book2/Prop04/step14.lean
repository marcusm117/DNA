import SystemE
import Book.Prop29
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_cnbe
import Book2.Prop04.step9_cfbe
import Book2.Prop04.step9_gnab
import Book2.Prop04.step9_knab
import Book2.Prop04.step14_ks
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.14: ∠ k:b:c + ∠ g:c:b = ∟ + ∟. CG (on CF) ∥ BK (on BE), cut by the transversal CB (on AB);
   the two co-interior angles at b and c sum to two right angles [Prop.~1.29] (proposition_29''''').
   The parallel ¬BE.intersectsLine CF is the shared step9_cfbe; k.sameSide g AB (the two interior
   feet on one side of the base) is step14_ks. -/
theorem helper_2_4_step14 (a b c d e g k : Point) (AB CF AD BE HK BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    ∠ k:b:c + ∠ g:c:b = ∟ + ∟ := by
  euclid_intros
  -- c on AB (between a, b); b ≠ c
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have had : a ≠ d := by euclid_finish
  -- root off-line facts
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have hbd : b ≠ d := fun h => step8_dnab (h ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  -- line distinctness from off-line points
  have hADCF : AD ≠ CF := fun h => step5_cnad (h ▸ hcCF)
  have hBEAD : BE ≠ AD := fun h => step9_anbe (h ▸ haAD)
  have step9_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_4_step9_cnbe a b c AB BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬(a.onLine BE); assumption)))
  have hCFBE : CF ≠ BE := fun h => step9_cnbe (h ▸ hcCF)
  have step9_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_4_step9_cfbe CF AD BE (by euclid_assumption "" (show CF ≠ BE; assumption)) (by euclid_assumption "" (show BE ≠ AD; assumption)) (by euclid_assumption "" (show AD ≠ CF; assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  -- k ∉ AB (k on HK ∥ AB), giving the interior distinctness c ≠ g and b ≠ k
  have step9_knab : ¬(k.onLine AB) := by euclid_apply (helper_2_4_step9_knab g k AB HK (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  have hcg : c ≠ g := fun h => step9_gnab (h ▸ hcAB)
  have hbk : b ≠ k := fun h => step9_knab (h ▸ hbAB)
  have step14_ks : k.sameSide g AB := by euclid_apply (helper_2_4_step14_ks g k AB HK (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)))
  euclid_apply (proposition_29''''' k g b c BE CF AB)
  euclid_finish

end Elements.Book2
