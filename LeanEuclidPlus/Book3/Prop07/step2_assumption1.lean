import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

theorem helper_3_7_step2_assumption1 (ABCD : Circle) (a d e f b : Point) (AD BE BF : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hb : b.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (h_bne_a : b ≠ a) (h_bne_d : b ≠ d)
    : formTriangle e b f BE BF AD := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have he_inside : e.insideCircle ABCD := by euclid_finish
  have hbAD : ¬(b.onLine AD) := by
    intro hbonAD
    -- e is inside the circle; b and d are on the circle; b ≠ d → e is between b and d
    have hbet_bed : between b e d :=
      circle_line_intersections e b d AD ABCD ⟨heAD, hbonAD, hdAD, he_inside, hb, hd, h_bne_d⟩
    -- e is between a and d, and e is between b and d → b = a (same side, same radius)
    have hba : b = a := by euclid_finish
    exact h_bne_a hba
  have hfe : f ≠ e := by euclid_finish
  have hfBE : ¬(f.onLine BE) :=
    offLine_of_two_points f e b AD BE hfAD heAD hfe heBE hbBE hbAD
  refine ⟨⟨heBE, hbBE, ?_⟩, hbBF, hfBF, hfAD, heAD,
    (line_ne_of_offLine f BF BE hfBF hfBE).symm,
    line_ne_of_offLine b BF AD hbBF hbAD,
    (line_ne_of_offLine b BE AD hbBE hbAD).symm⟩
  euclid_finish

end Elements.Book3
