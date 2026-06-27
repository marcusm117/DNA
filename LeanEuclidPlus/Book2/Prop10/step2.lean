import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step2 (2.10.2): CE = AC = CB. |c─e| = |a─c| from the prop-3 cut;
-- |c─e| = |c─b| by transitivity with the hypothesis |a─c| = |c─b|.
theorem helper_2_10_step2
  (a b c e : Point)
  (hce_ac : |(c─e)| = |(a─c)|)
  (hac_cb : |(a─c)| = |(c─b)|) :
  |(c─e)| = |(a─c)| ∧ |(c─e)| = |(c─b)| := by
  euclid_finish

end Elements.Book2
