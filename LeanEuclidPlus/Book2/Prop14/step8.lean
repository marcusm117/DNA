import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 8: H lies on the semicircle ⇒ |g─h| = |g─b₀| (both are radii; from point_on_circle_onlyif).
theorem helper_2_14_step8 (g h b₀ : Point) (hr : |(g─h)| = |(g─b₀)|) :
    |(g─h)| = |(g─b₀)| := hr

end Elements.Book2
