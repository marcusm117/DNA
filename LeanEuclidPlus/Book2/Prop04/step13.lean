import SystemE
import Book2.Prop04.step13_kbc
import Book2.Prop04.step13_sum
import Book2.Prop04.step13_bcg
import Book2.Prop04.step13_opp
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.13: "So I say that (it is) also right-angled." Announces the four right angles of CGKB. Since
   this sentence precedes 2.4.14–2.4.17 (which prove them), it re-derives the four angles here from the
   construction, reusing the same helper logic: ∠ k:b:c = ∟ (step15, square corner), the co-interior
   sum ∠ k:b:c + ∠ g:c:b = ∟+∟ (step14) ⟹ ∠ b:c:g = ∟ (step16), and the opposite angles
   ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ (step17). -/
theorem helper_2_4_step13 (a b c d e g k : Point) (AB CF AD BE HK BD DE : Line)
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
    (hbc : |(b─c)| = |(c─g)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟) := by
  euclid_intros
  have step13_kbc : ∠ k:b:c = ∟ := by euclid_apply (helper_2_4_step13_kbc a b c d e g k AB CF AD BE HK BD DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show k.onLine BE; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have step13_sum : ∠ k:b:c + ∠ g:c:b = ∟ + ∟ := by euclid_apply (helper_2_4_step13_sum a b c d e g k AB CF AD BE HK BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine BE; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have step13_bcg : ∠ b:c:g = ∟ := by euclid_apply (helper_2_4_step13_bcg a b c g k (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show |(b─c)| = |(c─g)|; assumption)) (by euclid_assumption "" (show ∠ k:b:c + ∠ g:c:b = ∟ + ∟; assumption)) (by euclid_assumption "" (show ∠ k:b:c = ∟; assumption)))
  have step13_opp : ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ := by euclid_apply (helper_2_4_step13_opp a b c d e g k AB CF AD BE HK BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CF; assumption)) (by euclid_assumption "" (show g.onLine CF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine BE; assumption)) (by euclid_assumption "" (show ¬(HK.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CF.intersectsLine AD); assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)) (by euclid_assumption "" (show ∠ k:b:c = ∟; assumption)) (by euclid_assumption "" (show ∠ b:c:g = ∟; assumption)))
  exact ⟨step13_kbc, step13_bcg, step13_opp.1, step13_opp.2⟩

end Elements.Book2
