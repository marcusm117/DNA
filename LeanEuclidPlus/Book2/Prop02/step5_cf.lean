import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

set_option systemE.solverTime 30 in
/- sub-fact for 2.2.5: c ≠ f. f lies on DE and c on AB; if c = f then c ∈ DE, giving a common
   point of DE and AB. With DE ≠ AB (step5_cf_dene), intersection_lines_common_point yields DE
   intersects AB — contradiction. -/
theorem helper_2_2_step5_cf (c f : Point) (AB DE : Line)
    (hDEAB2 : DE ≠ AB)
    (hcAB : c.onLine AB) (hfDE : f.onLine DE)
    (hDEAB : ¬(DE.intersectsLine AB)) :
    c ≠ f := by
  euclid_intros
  by_contra hcon
  euclid_apply (intersection_lines_common_point c DE AB)
  euclid_finish

end Elements.Book2
