import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.13: "So I say that (it is) also right-angled." Announces the four right angles of CGKB. Since
   this sentence precedes 2.4.14–2.4.17 (which prove them), it re-derives the four angles here from the
   construction, reusing the same helper logic: ∠ k:b:c = ∟ (step15, square corner), the co-interior
   sum ∠ k:b:c + ∠ g:c:b = ∟+∟ (step14) ⟹ ∠ b:c:g = ∟ (step16), and the opposite angles
   ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ (step17). -/
set_option systemE.solverTime 30 in
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
  have step13_kbc : ∠ k:b:c = ∟ := by sorry
  have step13_sum : ∠ k:b:c + ∠ g:c:b = ∟ + ∟ := by sorry
  have step13_bcg : ∠ b:c:g = ∟ := by sorry
  have step13_opp : ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ := by sorry
  exact ⟨step13_kbc, step13_bcg, step13_opp.1, step13_opp.2⟩

end Elements.Book2
