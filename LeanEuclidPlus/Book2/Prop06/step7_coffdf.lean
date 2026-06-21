import SystemE
import Book2.Prop06.step7_foffab
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: c ∉ DF. If c ∈ DF then c, d (distinct on AB, c ≠ d from between a c b / between a b d)
   both lie on DF, so DF = AB (two_points_determine_line), putting f ∈ AB — contradicting step7_foffab
   (the ∠c:d:f degeneracy). -/
theorem helper_2_6_step7_coffdf (a b c d f : Point) (AB DF : Line)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hdf : |(d─f)| = |(c─d)|) (hcdf : ∠ c:d:f = ∟) :
    ¬(c.onLine DF) := by
  have step7_foffab : ¬(f.onLine AB) := by euclid_apply (helper_2_6_step7_foffab a b c d f AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  intro hcDF
  euclid_apply (two_points_determine_line c d DF AB)
  euclid_finish

end Elements.Book2
