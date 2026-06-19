import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.1: the square CEFB on CB [Prop.~1.46]. The square's defining length/angle facts are
   produced by the proposition_46 construction in Main; this helper just repackages them. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step1 (b c e f : Point)
    (hce : |(c─e)| = |(c─b)|) (hbf : |(b─f)| = |(c─b)|) (hef : |(e─f)| = |(c─b)|)
    (hbce : ∠ b:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcbf : ∠ c:b:f = ∟) (hbfe : ∠ b:f:e = ∟) :
    |(c─e)| = |(c─b)| ∧ |(b─f)| = |(c─b)| ∧ |(e─f)| = |(c─b)| ∧
      (∠ b:c:e = ∟) ∧ (∠ c:e:f = ∟) ∧ (∠ c:b:f = ∟) ∧ (∠ b:f:e = ∟) := by
  exact ⟨hce, hbf, hef, hbce, hcef, hcbf, hbfe⟩

end Elements.Book2
