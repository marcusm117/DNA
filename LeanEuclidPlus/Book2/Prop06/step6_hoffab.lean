import SystemE
import Book2.Prop06.step2_eoff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- sub-fact for 2.6.6 / step6_lc: h ∉ AB. h lies on the diagonal DE and on BG. e ∉ AB (reuse
   step2_eoff, the right-angle degeneracy). If h ∈ AB then h and d (both on DE, d on AB) would force
   DE = AB (unless h = d), putting e ∈ AB — contradiction; and h = d is impossible since h is on BG
   with b (b ≠ d as d is beyond b on AB), off the top line through d. -/
theorem helper_2_6_step6_hoffab (a b c d e h : Point) (AB CE DE BG : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hBGCE : ¬(BG.intersectsLine CE)) :
    ¬(h.onLine AB) := by
  euclid_intros
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_finish

end Elements.Book2
