import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop11.step_nhout_hon
import Book3.Prop11.step_nhout_hin
open Classical
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g h : Point) (ABC ADE : Circle)
    (left : a.onCircle ABC) (left_1 : a.onCircle ADE)
    (left_2 : ¬ABC.intersectsCircle ADE) (left_3 : g.insideCircle ABC)
    (left_4 : f.isCentre ABC) (left_5 : g.isCentre ADE) (right_5 : f ≠ g)
    (hradii : |(g─a)| < |(f─a)|)
    (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_not_out : ¬h.outsideCircle ADE)
    : False := by
  by_cases hh_on : h.onCircle ADE
  · -- h is on both ABC and ADE; same-radius equalities force between f g a, contradicting hsuppose1
    have step_nhout_hon : False := by euclid_apply (helper_3_11_step_nhout_hon a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)) (by euclid_assumption "" (show h ≠ a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show h.onCircle ADE; assumption)))
    exact step_nhout_hon
  · -- h is strictly inside ADE
    have hh_in : h.insideCircle ADE := by
      by_contra h_not_in
      exact h_not_out ⟨h_not_in, hh_on⟩
    have step_nhout_hin : False := by euclid_apply (helper_3_11_step_nhout_hin a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)) (by euclid_assumption "" (show h ≠ a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show ¬h.onCircle ADE; assumption)) (by euclid_assumption "" (show h.insideCircle ADE; assumption)))
    exact step_nhout_hin

end Elements.Book3
