import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step9
    (ABCD : Circle) (a d e f c g : Point) (AD CE GE : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hc : c.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (h_ang : ∠ c:e:f > ∠ g:e:f)
    (h_cne_a : c ≠ a) (h_cne_d : c ≠ d)
    (h_gne_a : g ≠ a) (h_gne_d : g ≠ d)
    : |(f─c)| > |(f─g)| := by
  euclid_apply (line_from_points c f) as CF
  euclid_apply (line_from_points g f) as GF
  have step9_tri_ecf : formTriangle e c f CE CF AD := by sorry
  have step9_tri_egf : formTriangle e g f GE GF AD := by sorry
  have h24 := Elements.Book1.proposition_24 e c f e g f CE CF AD GE GF AD
  linarith [segment_symmetric f c, segment_symmetric f g,
            h24 ⟨step9_tri_ecf, step9_tri_egf, by euclid_finish, rfl, h_ang⟩]

end Elements.Book3
