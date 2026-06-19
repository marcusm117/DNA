import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: |l─e| = |c─d|. Length arithmetic on the two collinear triples:
   between c l e ⟹ |c─e| = |c─l| + |l─e|;  between c d b ⟹ |c─b| = |c─d| + |d─b|.
   With |c─e| = |c─b| (square side), |c─l| = |d─h| (CDHL parallelogram), |d─h| = |d─b| (step13),
   we get |c─l| = |d─b|, hence |l─e| = |c─e| − |c─l| = |c─b| − |d─b| = |c─d|. -/
theorem helper_2_5_step15_le_cd (b c d e l h : Point)
    (hcle : between c l e) (hcdb : between c d b)
    (hce_cb : |(c─e)| = |(c─b)|)
    (hcl_dh : |(c─l)| = |(d─h)|)
    (hdh_db : |(d─h)| = |(d─b)|) :
    |(l─e)| = |(c─d)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
