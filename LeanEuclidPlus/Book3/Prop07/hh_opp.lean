import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_7_hh_opp
    (ABCD : Circle) (a b c d e f g h : Point) (AD : Line)
    (h_ctr : e.isCentre ABCD)
    (ha : a.onCircle ABCD) (hd : d.onCircle ABCD) (hg : g.onCircle ABCD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hbet_aed : between a e d) (hbet_efd : between e f d)
    (hg_ne_a : g ≠ a) (hg_ne_d : g ≠ d)
    (step4 : |(f─a)| > |(f─b)|)
    (step7 : |(b─f)| > |(c─f)|)
    (step9 : |(f─c)| > |(f─g)|)
    (step28 : ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h)
    : h.opposingSides g AD := by
  have heAD : e.onLine AD := between_same_line_in a e d AD ⟨hbet_aed, haAD, hdAD⟩
  have hfAD : f.onLine AD := between_same_line_in e f d AD ⟨hbet_efd, heAD, hdAD⟩
  have hef : e ≠ f := by euclid_finish
  have he_inside : e.insideCircle ABCD := center_inside_circle e ABCD h_ctr
  have hgAD : ¬(g.onLine AD) := by
    intro hgon
    have hbgd := circle_line_intersections e g d AD ABCD ⟨heAD, hgon, hdAD, he_inside, hg, hd, hg_ne_d⟩
    exact hg_ne_a (by euclid_finish)
  have hfg : f ≠ g := fun heq => hgAD (heq ▸ hfAD)
  obtain ⟨β, hβ_ctr, hgβ⟩ := circle_from_points f g hfg
  have hne : ABCD ≠ β := fun heq => hef (centre_unique e f ABCD ⟨h_ctr, heq ▸ hβ_ctr⟩)
  have hf_β : f.insideCircle β := center_inside_circle f β hβ_ctr
  have haβ : a.outsideCircle β := by euclid_finish
  have hfno : ¬(f.outsideCircle ABCD) := by euclid_finish
  have hano : ¬(a.outsideCircle ABCD) := by euclid_finish
  have hinters : ABCD.intersectsCircle β :=
    intersection_circle_circle_1 f a ABCD β ⟨hfno, hano, hf_β, haβ⟩
  obtain ⟨p, hp_ABCD, hp_β, hp_opp⟩ :=
    intersection_opposite_side ABCD β g e f AD ⟨hinters, h_ctr, hβ_ctr, heAD, hfAD, hgAD⟩
  have hfp : |(f─p)| = |(f─g)| :=
    point_on_circle_onlyif f g p β ⟨hβ_ctr, hgβ, hp_β⟩
  rcases step28 p hp_ABCD hfp with heq | heq
  · rw [heq] at hp_opp
    exact absurd (same_side_rfl g AD hgAD) hp_opp.2.2
  · rw [heq] at hp_opp
    exact hp_opp

end Elements.Book3
