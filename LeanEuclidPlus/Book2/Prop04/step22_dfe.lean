import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.22 sub: f (= CF ∩ DE) is between d and e on the bottom DE. CF separates d from e: a, b are on
   opposite sides of CF (c ∈ CF is between a, b on AB — pasch_3); a.sameSide d CF (a, d on AD ∥ CF)
   and b.sameSide e CF (b, e on BE ∥ CF); hence d, e are on opposite sides of CF, and f (= DE ∩ CF)
   lies between them (pasch_4). The two sameSide facts and the opposite-sides chain are passed in. -/
theorem helper_2_4_step22_dfe (a b c d e f : Point) (DE CF AB AD BE : Line)
    (hacb : between a c b)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdf : d ≠ f) (hef : e ≠ f) (hde : d ≠ e)
    (hadsCF : a.sameSide d CF) (hbesCF : b.sameSide e CF) :
    between d f e := by
  euclid_intros
  -- a, b on opposite sides of CF (c between them, c ∈ CF)
  euclid_apply (pasch_3 a c b CF)
  euclid_apply (pasch_4 d f e CF DE)
  euclid_finish

end Elements.Book2
