import SystemE
import Book2.Prop06.step7_foffab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: a ∉ DF. If a ∈ DF then a, d (distinct on AB, a ≠ d from between a c b / between a b d)
   both lie on DF, so DF = AB (two_points_determine_line), putting f ∈ AB — contradicting step7_foffab
   (the ∠c:d:f degeneracy). -/
theorem helper_2_6_step9_aoffdf (a b c d f : Point) (AB DF : Line)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hdf : |(d─f)| = |(c─d)|) (hcdf : ∠ c:d:f = ∟) :
    ¬(a.onLine DF) := by
  have step7_foffab : ¬(f.onLine AB) := by euclid_apply (helper_2_6_step7_foffab a b c d f AB (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)))
  intro haDF
  euclid_apply (two_points_determine_line a d DF AB)
  euclid_finish

end Elements.Book2
