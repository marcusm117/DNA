import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.2: "and let the (rest of) the figure be drawn." Asserts the defining facts of the
   lines drawn: BD joined (distinct points b,d on BD), CN through C parallel to AD, and HF
   through G parallel to AB. All incidence/parallel facts are deposited by the Main
   constructions; the only fact to derive is b ≠ d, via d ∉ AB (step2_dnab) and b ∈ AB. -/
set_option systemE.solverTime 30 in
theorem helper_2_7_step2 (a b c d e n g h f : Point) (AB DE AD BE BD CN HF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadlen : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hcCN : c.onLine CN) (hCNAD : ¬CN.intersectsLine AD)
    (hgHF : g.onLine HF) (hHFAB : ¬HF.intersectsLine AB) :
    distinctPointsOnLine b d BD ∧ (c.onLine CN ∧ ¬(CN.intersectsLine AD)) ∧
      (g.onLine HF ∧ ¬(HF.intersectsLine AB)) := by
  have step2_dnab : ¬(d.onLine AB) := by sorry
  euclid_finish

end Elements.Book2
