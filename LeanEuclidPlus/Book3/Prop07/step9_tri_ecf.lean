import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

theorem helper_3_7_step9_tri_ecf
    (ABCD : Circle) (a d e f c : Point) (AD CE CF : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hc : c.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hcCF : c.onLine CF) (hfCF : f.onLine CF)
    (h_cne_a : c ≠ a) (h_cne_d : c ≠ d)
    : formTriangle e c f CE CF AD := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have he_inside : e.insideCircle ABCD := by euclid_finish
  have hcAD : ¬(c.onLine AD) := by
    intro hconAD
    have hbet_ced : between c e d :=
      circle_line_intersections e c d AD ABCD ⟨heAD, hconAD, hdAD, he_inside, hc, hd, h_cne_d⟩
    have hca : c = a := by euclid_finish
    exact h_cne_a hca
  have hfe : f ≠ e := by euclid_finish
  have hfCE : ¬(f.onLine CE) :=
    offLine_of_two_points f e c AD CE hfAD heAD hfe heCE hcCE hcAD
  refine ⟨⟨heCE, hcCE, ?_⟩, hcCF, hfCF, hfAD, heAD,
    (line_ne_of_offLine f CF CE hfCF hfCE).symm,
    line_ne_of_offLine c CF AD hcCF hcAD,
    (line_ne_of_offLine c CE AD hcCE hcAD).symm⟩
  euclid_finish

end Elements.Book3
