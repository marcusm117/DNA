import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

theorem helper_3_7_step9_tri_egf
    (ABCD : Circle) (a d e f g : Point) (AD GE GF : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (h_gne_a : g ≠ a) (h_gne_d : g ≠ d)
    : formTriangle e g f GE GF AD := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have he_inside : e.insideCircle ABCD := by euclid_finish
  have hgAD : ¬(g.onLine AD) := by
    intro hgonAD
    have hbet_ged : between g e d :=
      circle_line_intersections e g d AD ABCD ⟨heAD, hgonAD, hdAD, he_inside, hg, hd, h_gne_d⟩
    have hga : g = a := by euclid_finish
    exact h_gne_a hga
  have hfe : f ≠ e := by euclid_finish
  have hfGE : ¬(f.onLine GE) :=
    offLine_of_two_points f e g AD GE hfAD heAD hfe heGE hgGE hgAD
  refine ⟨⟨heGE, hgGE, ?_⟩, hgGF, hfGF, hfAD, heAD,
    (line_ne_of_offLine f GF GE hfGF hfGE).symm,
    line_ne_of_offLine g GF AD hgGF hgAD,
    (line_ne_of_offLine g GE AD hgGE hgAD).symm⟩
  euclid_finish

end Elements.Book3
