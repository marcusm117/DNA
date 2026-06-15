import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.31 sub: g (= CF ∩ HK) is between c and f on the vertical CF. HK separates c (on AB, above)
   from f (on DE, below): c.sameSide a HK... rather, the points c and f lie on opposite sides of HK,
   and g = CF ∩ HK lies between them (pasch_4). The opposite-sides fact ¬(c.sameSide f HK) is passed
   in (derived from c above / f below HK). -/
theorem helper_2_4_step31_cgf (c f g : Point) (CF HK : Line)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF) (hgCF : g.onLine CF)
    (hgHK : g.onLine HK)
    (hcg : c ≠ g) (hfg : f ≠ g) (hcf : c ≠ f) (hHKCF : HK ≠ CF)
    (hcfHK : ¬(c.sameSide f HK)) :
    between c g f := by
  euclid_intros
  euclid_apply (pasch_4 c g f HK CF)
  euclid_finish

end Elements.Book2
