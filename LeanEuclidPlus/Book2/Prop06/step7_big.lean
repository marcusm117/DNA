import SystemE
import Book2.Prop06.step7_ssdc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: the square CEFD as formParallelogram d f c e DF CE AB EF (d,f on DF; c,e on CE;
   d,c on AB; f,e on EF). The derived facts are f ≠ e (e off DF via e.sameSide c DF, f ∈ DF) and the
   hard conjunct d.sameSide c EF (d,c on AB ∥ EF, off EF and not separable) — its own sub-leaf. -/
theorem helper_2_6_step7_big (a b c d e f : Point) (AB DF CE EF : Line)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdAB : d.onLine AB) (hcAB : c.onLine AB) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (hacb : between a c b) (habd : between a b d) (hce : |(c─e)| = |(c─d)|)
    (hCEDF : ¬(CE.intersectsLine DF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hecDF : e.sameSide c DF) (hdce : ∠ d:c:e = ∟) :
    formParallelogram d f c e DF CE AB EF := by
  euclid_intros
  have step7_ssdc : d.sameSide c EF := by euclid_apply (helper_2_6_step7_ssdc a b c d e AB EF CE (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  have hfe : f ≠ e := by euclid_finish
  euclid_finish

end Elements.Book2
