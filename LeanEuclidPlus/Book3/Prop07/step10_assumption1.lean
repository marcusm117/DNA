import SystemE
import Book1.Prop20.Main
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

set_option systemE.solverTime 30 in
theorem helper_3_7_step10_assumption1
    (ABCD : Circle) (a d e f g : Point) (AD GE : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (h_gne_a : g ≠ a) (h_gne_d : g ≠ d)
    : |(g─f)| + |(f─e)| > |(g─e)| := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have he_inside : e.insideCircle ABCD := by euclid_finish
  have hgAD : ¬(g.onLine AD) := by
    intro hgonAD
    have : between g e d :=
      circle_line_intersections e g d AD ABCD ⟨heAD, hgonAD, hdAD, he_inside, hg, hd, h_gne_d⟩
    exact h_gne_a (by euclid_finish)
  euclid_apply (line_from_points g f) as GF
  have hgGF : g.onLine GF := by euclid_finish
  have hfGF : f.onLine GF := by euclid_finish
  have hfe : f ≠ e := by euclid_finish
  have hgf : g ≠ f := fun h => hgAD (h ▸ hfAD)
  have hfoffGE : ¬(f.onLine GE) :=
    offLine_of_two_points f e g AD GE hfAD heAD hfe heGE hgGE hgAD
  have hGE_ne_GF : GE ≠ GF := fun heq => hfoffGE (heq.symm ▸ hfGF)
  have h_tri : formTriangle g f e GF AD GE :=
    ⟨⟨hgGF, hfGF, hgf⟩, hfAD, heAD, heGE, hgGE,
     line_ne_of_offLine g GF AD hgGF hgAD,
     (line_ne_of_offLine g GE AD hgGE hgAD).symm,
     hGE_ne_GF⟩
  euclid_apply (Elements.Book1.proposition_20 g f e GF AD GE)
  linarith

end Elements.Book3
