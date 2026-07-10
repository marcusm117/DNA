import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_step26
    (ABCD : Circle) (a b c d e f g h k : Point) (AD : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (hh_on : h.onCircle ABCD) (hk_on : k.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hg_ne_a : g ≠ a) (hg_ne_d : g ≠ d)
    (hk_ne_g : k ≠ g) (hk_ne_h : k ≠ h) (hh_ne_g : h ≠ g)
    (step4 : |(f─a)| > |(f─b)|)
    (step7 : |(b─f)| > |(c─f)|)
    (step9 : |(f─c)| > |(f─g)|)
    (step14 : |(f─g)| > |(f─d)|)
    (step21 : |(f─g)| = |(f─h)|)
    (hk_eq : |(f─k)| = |(f─g)|)
    : False := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have hef : e ≠ f := by euclid_finish
  have he_inside : e.insideCircle ABCD := center_inside_circle e ABCD h_ctr
  have hgAD : ¬(g.onLine AD) := by
    intro hgon
    have hbgd := circle_line_intersections e g d AD ABCD ⟨heAD, hgon, hdAD, he_inside, hg, hd, hg_ne_d⟩
    exact hg_ne_a (by euclid_finish)
  have hfg : f ≠ g := fun heq => hgAD (heq ▸ hfAD)
  have hkAD : ¬(k.onLine AD) := by
    intro hkon
    have hk_ne_a : k ≠ a := by euclid_finish
    have hk_ne_d : k ≠ d := by euclid_finish
    have hbkd := circle_line_intersections e k d AD ABCD ⟨heAD, hkon, hdAD, he_inside, hk_on, hd, hk_ne_d⟩
    exact hk_ne_a (by euclid_finish)
  have hhAD : ¬(h.onLine AD) := by
    intro hhon
    have hh_ne_a : h ≠ a := by euclid_finish
    have hh_ne_d : h ≠ d := by euclid_finish
    have hbhd := circle_line_intersections e h d AD ABCD ⟨heAD, hhon, hdAD, he_inside, hh_on, hd, hh_ne_d⟩
    exact hh_ne_a (by euclid_finish)
  obtain ⟨β, hβ_ctr, hgβ⟩ := circle_from_points f g hfg
  have hne : ABCD ≠ β := fun heq => hef (centre_unique e f ABCD ⟨h_ctr, heq ▸ hβ_ctr⟩)
  have hkβ : k.onCircle β := point_on_circle_if f g k β ⟨hβ_ctr, hgβ, hk_eq⟩
  have hhβ : h.onCircle β := point_on_circle_if f g h β ⟨hβ_ctr, hgβ, step21.symm⟩
  have hdiff_kg := circles_intersections_diff_side e f k g ABCD β AD
    ⟨hne, hk_on, hkβ, hg, hgβ, hk_ne_g, h_ctr, hβ_ctr, heAD, hfAD⟩
  have hdiff_kh := circles_intersections_diff_side e f k h ABCD β AD
    ⟨hne, hk_on, hkβ, hh_on, hhβ, hk_ne_h, h_ctr, hβ_ctr, heAD, hfAD⟩
  have hdiff_gh := circles_intersections_diff_side e f g h ABCD β AD
    ⟨hne, hg, hgβ, hh_on, hhβ, hh_ne_g.symm, h_ctr, hβ_ctr, heAD, hfAD⟩
  rcases same_side_pigeon_hole k g h AD ⟨hkAD, hgAD, hhAD⟩ with h1 | h2 | h3
  · exact hdiff_kg h1
  · exact hdiff_kh h2
  · exact hdiff_gh h3

end Elements.Book3
