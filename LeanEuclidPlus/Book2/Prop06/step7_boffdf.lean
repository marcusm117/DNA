import SystemE
import Book2.Prop06.step7_foffab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: b ∉ DF. If b ∈ DF then b, d (distinct on AB, b ≠ d from between a b d) both lie on DF,
   so DF = AB (two_points_determine_line), putting f ∈ AB — contradicting step7_foffab (the ∠c:d:f
   degeneracy). -/
theorem helper_2_6_step7_boffdf (a b c d f : Point) (AB DF : Line)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hdf : |(d─f)| = |(c─d)|) (hcdf : ∠ c:d:f = ∟) :
    ¬(b.onLine DF) := by
  have step7_foffab : ¬(f.onLine AB) := by euclid_apply (helper_2_6_step7_foffab a b c d f AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  intro hbDF
  euclid_apply (two_points_determine_line b d DF AB)
  euclid_finish

end Elements.Book2
