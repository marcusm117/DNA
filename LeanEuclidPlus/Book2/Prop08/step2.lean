import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step2 (a d e f : Point)
    (h_ef : |(e─f)| = |(a─d)|) (h_ae : |(a─e)| = |(a─d)|)
    (h_df : |(d─f)| = |(a─d)|) (h_dae : ∠ d:a:e = ∟)
    (h_aef : ∠ a:e:f = ∟) (h_adf : ∠ a:d:f = ∟)
    (h_dfe : ∠ d:f:e = ∟) :
    |(e─f)| = |(a─d)| ∧ |(a─e)| = |(a─d)| ∧ |(d─f)| = |(a─d)| ∧
      (∠ d:a:e = ∟) ∧ (∠ a:e:f = ∟) ∧ (∠ a:d:f = ∟) ∧ (∠ d:f:e = ∟) := by
  exact ⟨h_ef, h_ae, h_df, h_dae, h_aef, h_adf, h_dfe⟩

end Elements.Book2
