import SystemE
import Mathlib.Tactic.Linarith
open Classical
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- hradii (|g-a| < |f-a|, i.e. r_ADE < r_ABC) pins ADE as the INNER circle. Without it the reductio is
-- unsound: `g.insideCircle ABC` alone admits ABC-inside-ADE, in which h inside ADE gives no contradiction.
theorem helper_3_11_step_nhout_hin (a f g h : Point) (ABC ADE : Circle)
    (left : a.onCircle ABC) (left_1 : a.onCircle ADE)
    (left_2 : ¬ABC.intersectsCircle ADE) (left_3 : g.insideCircle ABC)
    (left_4 : f.isCentre ABC) (left_5 : g.isCentre ADE) (right_5 : f ≠ g)
    (hradii : |(g─a)| < |(f─a)|)
    (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (hh_on : ¬h.onCircle ADE) (hh_in : h.insideCircle ADE)
    : False := by
  have hg_in_ADE : g.insideCircle ADE := center_inside_circle g ADE left_5
  euclid_apply (line_from_points f g) as FG
  have hg_on_FG : g.onLine FG := by euclid_finish
  have hf_on_FG : f.onLine FG := by euclid_finish
  have hh_on_FG : h.onLine FG :=
    between_same_line_out f g h FG ⟨h_bet_fgh, hf_on_FG, hg_on_FG⟩
  have hgh_ne : g ≠ h := by euclid_finish
  obtain ⟨pf, hpf_ADE, hpf_FG, hpf_bet⟩ :=
    intersection_circle_line_extending_points ADE FG g h ⟨hg_in_ADE, hg_on_FG, hh_on_FG, hgh_ne⟩
  have hpf_in_ABC : pf.insideCircle ABC := by euclid_finish
  exact left_2 (intersection_circle_circle_2 h pf ABC ADE h_on_ABC hpf_in_ABC hh_in hpf_ADE)

end Elements.Book3
