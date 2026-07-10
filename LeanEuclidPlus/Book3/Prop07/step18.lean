import SystemE
import Book1.Prop23.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_7_step18
    (ABCD : Circle) (a d e f g h : Point) (AD GE FH : Line)
    (h_ctr : e.isCentre ABCD)
    (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (hh_on : h.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hgGE : g.onLine GE) (heGE : e.onLine GE)
    (hfFH : f.onLine FH) (hhFH : h.onLine FH)
    (hg_ne_a : g ≠ a) (hg_ne_d : g ≠ d)
    (hh_ang_pre : ∠ f:e:h = ∠ g:e:f)
    : ∠ f:e:h = ∠ g:e:f ∧ distinctPointsOnLine f h FH := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have _h23 : ∃ p, p ≠ e ∧ (∠ p:e:f = ∠ g:e:f) := by
    euclid_apply (Elements.Book1.proposition_23 e f e g f AD GE AD)
    exact ⟨_, by assumption, by assumption⟩
  have hf_inside : f.insideCircle ABCD := by euclid_finish
  refine ⟨hh_ang_pre, hfFH, hhFH, ?_⟩
  euclid_finish

end Elements.Book3
