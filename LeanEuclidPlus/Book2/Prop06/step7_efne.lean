import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: EF ≠ AB. e ∈ EF but e ∉ AB — e ∉ AB reuses step2_eoff (the right-angle degeneracy). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step7_efne (a b c d e : Point) (AB CE EF : Line)
    (heEF : e.onLine EF)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟) :
    EF ≠ AB := by
  have step2_eoff : ¬(e.onLine AB) := by sorry
  exact fun heq => step2_eoff (heq ▸ heEF)

end Elements.Book2
