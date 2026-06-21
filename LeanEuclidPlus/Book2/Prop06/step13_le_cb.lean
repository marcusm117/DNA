import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.13 sub: |l─e| = |c─b|. Length arithmetic on the two collinear triples:
   between c l e ⟹ |c─e| = |c─l| + |l─e|;  between c b d ⟹ |c─d| = |c─b| + |b─d|.
   With |c─e| = |c─d| (square side), |c─l| = |b─h| (CBHL parallelogram), |b─h| = |b─d| (step11_bdbh),
   we get |c─l| = |b─d|, hence |l─e| = |c─e| − |c─l| = |c─d| − |b─d| = |c─b|. -/
theorem helper_2_6_step13_le_cb (b c d e l h : Point)
    (hcle : between c l e) (hcbd : between c b d)
    (hce_cd : |(c─e)| = |(c─d)|)
    (hcl_bh : |(c─l)| = |(b─h)|)
    (hbd_bh : |(b─d)| = |(b─h)|) :
    |(l─e)| = |(c─b)| := by
  euclid_intros
  euclid_finish

end Elements.Book2
