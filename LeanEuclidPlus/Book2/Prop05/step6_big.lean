import SystemE
import Book2.Prop05.step6_big_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: the square CEFB as formParallelogram b f c e BF CE AB EF (b,f on BF; c,e on CE;
   b,c on AB; f,e on EF; distinct f,e on EF; b.sameSide c EF; BF ∥ CE; AB ∥ EF). The two derived
   facts are f ≠ e (e is off BF via e.sameSide c BF, f ∈ BF) and the hard conjunct b.sameSide c EF
   (b,c on AB ∥ EF, so off EF and not separable across it). -/
theorem helper_2_5_step6_big (a b c d e f : Point) (AB BF CE EF : Line)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (hacd : between a c d) (hcdb : between c d b) (hcelen : |(c─e)| = |(c─b)|)
    (hCEBF : ¬(CE.intersectsLine BF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hecBF : e.sameSide c BF) (hbce : ∠ b:c:e = ∟) :
    formParallelogram b f c e BF CE AB EF := by
  euclid_intros
  -- f ≠ e: e off BF (e.sameSide c BF), f ∈ BF. The hard conjunct b.sameSide c EF is its own sub-leaf;
  -- the rest of formParallelogram is incidences + the two parallels.
  have hfe : f ≠ e := by euclid_finish
  have step6_big_ss : b.sameSide c EF := by euclid_apply (helper_2_5_step6_big_ss a b c d e AB EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
