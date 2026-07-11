import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_hon (a f g h : Point) (ABC ADE : Circle)
    (left : a.onCircle ABC) (left_1 : a.onCircle ADE)
    (left_2 : ¬ABC.intersectsCircle ADE)
    (left_3 : g.insideCircle ABC)
    (left_4 : f.isCentre ABC) (left_5 : g.isCentre ADE) (right_5 : f ≠ g)
    (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (hh_on : h.onCircle ADE)
    : False := by
  have hg_in_ADE : g.insideCircle ADE := center_inside_circle g ADE left_5
  euclid_apply (line_from_points f g) as FG
  have hg_on_FG : g.onLine FG := by euclid_finish
  have hf_on_FG : f.onLine FG := by euclid_finish
  have hh_on_FG : h.onLine FG :=
    between_same_line_out f g h FG ⟨h_bet_fgh, hf_on_FG, hg_on_FG⟩
  have hgh_ne : g ≠ h := by euclid_finish
  -- Metric facts: h on both circles links the two radii
  have hgh_eq : |(g─h)| = |(g─a)| := by euclid_finish
  have hfh_eq : |(f─h)| = |(f─a)| := by euclid_finish
  have hbfgh := between_if f g h h_bet_fgh
  -- |f-g| + |g-a| = |f-a|
  have hfga_sum : |(f─g)| + |(g─a)| = |(f─a)| := by linarith
  -- Extend FG from h through g to h' on ABC (between h' g h)
  obtain ⟨h', hh'_ABC, hh'_FG, hbet_h'gh⟩ :=
    intersection_circle_line_extending_points ABC FG g h ⟨left_3, hg_on_FG, hh_on_FG, hgh_ne⟩
  -- hbet_h'gh : between h' g h (h' on left side of g, h on right)
  -- Supply metric for h'.outsideCircle ADE:
  -- |h'-g| + |g-a| = |h'-h| (from between h' g h + |g-h|=|g-a|)
  -- |f-h'| = |f-a| = |f-g| + |g-a| (h' on ABC)
  -- → between h' f g (ruling out between f h' g: |f-h'|+|h'-g|=|f-g| impossible since |f-h'|≥|f-g|+|g-a|>|f-g|)
  -- → |g-h'| = 2|f-g| + |g-a| > |g-a|
  have hbh'gh_sum := between_if h' g h hbet_h'gh
  have hfh'_eq : |(f─h')| = |(f─a)| := by euclid_finish
  have h'_out_ADE : h'.outsideCircle ADE := by euclid_finish
  -- g: inside ABC (not outside) and inside ADE
  -- h': on ABC (not outside ABC) and outside ADE
  -- intersection_circle_circle_1 g h' ABC ADE
  exact left_2 (intersection_circle_circle_1 g h' ABC ADE
    ⟨fun ⟨hc, _⟩ => hc left_3,
     fun ⟨_, hc⟩ => hc hh'_ABC,
     hg_in_ADE,
     h'_out_ADE⟩)

end Elements.Book3
