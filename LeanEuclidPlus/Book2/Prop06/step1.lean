import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.1: the square CEFD on CD [Prop.~1.46]. The square's defining length/angle facts are
   produced by the proposition_46 construction in Main; this helper just repackages them. -/
theorem helper_2_6_step1 (c d e f : Point)
    (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|) (hef : |(e─f)| = |(c─d)|)
    (hdce : ∠ d:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcdf : ∠ c:d:f = ∟) (hdfe : ∠ d:f:e = ∟) :
    |(c─e)| = |(c─d)| ∧ |(d─f)| = |(c─d)| ∧ |(e─f)| = |(c─d)| ∧
      (∠ d:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:d:f = ∟) ∧ (∠ d:f:e = ∟) := by
  exact ⟨hce, hdf, hef, hdce, hcef, hcdf, hdfe⟩

end Elements.Book2
