import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step 12: GF = GH (both radii of the semicircle): |g─f| = |b₀─g| = |g─h|.
theorem helper_2_14_step12 (g f h b₀ : Point)
    (h_mid : |(b₀─g)| = |(g─f)|) (h_rad : |(g─h)| = |(g─b₀)|) :
    |(g─f)| = |(g─h)| := by
  euclid_finish

end Elements.Book2
