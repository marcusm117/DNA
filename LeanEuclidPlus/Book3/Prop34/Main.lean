import SystemE
import Book1.Prop23.Main
import Book3.Prop32.Main
import Book3.Prop34.step1
import Book3.Prop34.step2
import Book3.Prop34.step3
import Book3.Prop34.step4
import Book3.Prop34.step5
import Book3.Prop34.hEF_exists
import Book3.Prop34.hpq
import Book3.Prop34.hBC_int
import Book3.Prop34.hc_ex
import Book3.Prop34.hef_choice
import Book3.Prop34.ha_exists
import Book3.Prop34.step3_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem proposition_34 : ∀ (ABC : Circle) (d1 d d2 : Point),
  d1 ≠ d ∧ d2 ≠ d →
  0 < ∠ d1:d:d2 → ∠ d1:d:d2 < ∟ + ∟ →
  ∃ (b c : Point), b.onCircle ABC ∧ c.onCircle ABC ∧ b ≠ c ∧
    ∃ a : Point, a.onCircle ABC ∧ ∠ b:a:c = ∠ d1:d:d2 :=
by
  euclid_intros
  euclid_intro_sentence "3.34.0"
    "To cut off a segment, accepting an angle equal to a given rectilinear angle, from a given circle. Let $ABC$ be the given circle, and $D$ the given rectilinear angle. So it is required to cut off a segment, accepting an angle equal to the given rectilinear angle $D$, from the given circle $ABC$."

  -- Get b on the circle ABC (tangent contact point)
  obtain ⟨b, hb_ABC⟩ := exists_point_on_circle ABC
  -- Tangent line EF at b, plus: every other line through b meets ABC (Porism to III.16)
  have hEF_exists : ∃ EF : Line, b.onLine EF ∧ ¬ EF.intersectsCircle ABC ∧
      (∀ FA : Line, b.onLine FA → FA ≠ EF → FA.intersectsCircle ABC) := by euclid_apply (helper_3_34_hEF_exists b ABC (by euclid_assumption "" (show b.onCircle ABC; assumption)))
  obtain ⟨EF, hb_EF, hEF_notint, hEF_others⟩ := hEF_exists

  euclid_sentence "3.34.1"
    "Let $EF$ be drawn touching $ABC$ at point $B$.$^\\dag$"
    (step1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC) := by euclid_apply (helper_3_34_step1 b ABC EF (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬ EF.intersectsCircle ABC; assumption)))

  -- Two points p, q straddling b on the tangent EF (e, f named later by side)
  have hpq : ∃ p q : Point, p.onLine EF ∧ q.onLine EF ∧ between p b q := by euclid_apply (helper_3_34_hpq b EF (by euclid_assumption "" (show b.onLine EF; assumption)))
  obtain ⟨p, q, hp_EF, hq_EF, hbet_pbq⟩ := hpq
  -- angle QBC₀ = D at B on the straight-line QB [Prop 1.23]
  euclid_apply (line_from_points d d1) as DD1
  euclid_apply (line_from_points d d2) as DD2
  euclid_apply (proposition_23 b q d d1 d2 EF DD1 DD2) as c₀
  have hbc₀ne : b ≠ c₀ := by euclid_finish
  -- Line BC through b and c₀ (the chord direction)
  euclid_apply (line_from_points b c₀) as BC
  -- BC is not the tangent, hence it meets the circle again
  have hBC_int : BC.intersectsCircle ABC := by euclid_apply (helper_3_34_hBC_int b c₀ p q d1 d d2 ABC EF BC (by euclid_assumption "" (show ∀ FA : Line, b.onLine FA → FA ≠ EF → FA.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c₀.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c₀; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show q.onLine EF; assumption)) (by euclid_assumption "" (show between p b q; assumption)) (by euclid_assumption "" (show ∠ c₀:b:q = ∠ d1:d:d2; assumption)) (by euclid_assumption "" (show 0 < ∠ d1:d:d2; assumption)) (by euclid_assumption "" (show ∠ d1:d:d2 < ∟ + ∟; assumption)))
  -- the far intersection c of chord BC with ABC (distinct from b)
  have hc_ex : ∃ c : Point, c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c := by euclid_apply (helper_3_34_hc_ex b ABC BC (by euclid_assumption "" (show BC.intersectsCircle ABC; assumption)))
  obtain ⟨c, hc_ABC, hc_BC, hbc_ne⟩ := hc_ex
  -- name e, f from {p, q} so that ∠ f:b:c = D (uses the p/q straddle symmetry)
  have hef_choice : ∃ e f : Point, e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
      ∠ f:b:c = ∠ d1:d:d2 := by euclid_apply (helper_3_34_hef_choice b c c₀ p q d1 d d2 ABC EF BC (by euclid_assumption "" (show p.onLine EF; assumption)) (by euclid_assumption "" (show q.onLine EF; assumption)) (by euclid_assumption "" (show between p b q; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c₀.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c₀; assumption)) (by euclid_assumption "" (show ∠ c₀:b:q = ∠ d1:d:d2; assumption)) (by euclid_assumption "" (show BC.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show ¬ EF.intersectsCircle ABC; assumption)))
  obtain ⟨e, f, he_EF, hf_EF, hbet_ebf, hangle_fbc⟩ := hef_choice

  euclid_sentence "3.34.2"
    "And let (angle) $FBC$, equal to angle $D$, be constructed on the straight-line $FB$, at the point $B$ on it [Prop.~1.23]."
    (step2 : ∠ f:b:c = ∠ d1:d:d2) := by euclid_apply (helper_3_34_step2 b c f d1 d d2 (by euclid_assumption "" (show ∠ f:b:c = ∠ d1:d:d2; assumption)))

  -- Get a in the alternate segment BAC (on ABC, opposite side of BC from f)
  have ha_exists : ∃ a : Point, a.onCircle ABC ∧ a.opposingSides f BC := by euclid_apply (helper_3_34_ha_exists b c e f ABC BC EF (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show BC.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show ¬ EF.intersectsCircle ABC; assumption)))
  obtain ⟨a, ha_ABC, ha_opp⟩ := ha_exists

  -- @assumption_valid
  have step3_assumption1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC := by euclid_finish
  -- @assumption_gap
  have step3_assumption2 : b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c := by euclid_apply (helper_3_34_step3_assumption2 b c ABC BC (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)))
  -- @suppress_deps_check "source cites [Prop.~1.32] (exterior-angle) but this is the alternate-segment theorem, Euclid III.32 = proposition_32"
  -- @assumption ("some straight-line $EF$ touches the circle $ABC$", b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC)
  -- @assumption ("$BC$ has been drawn across (the circle) from the point of contact $B$", b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c)
  euclid_sentence "3.34.3"
    "Therefore, since some straight-line $EF$ touches the circle $ABC$, and $BC$ has been drawn across (the circle) from the point of contact $B$, angle $FBC$ is thus equal to the angle constructed in the alternate segment $BAC$ [Prop.~1.32]."
    (step3 : ∠ f:b:c = ∠ b:a:c) := by euclid_apply (helper_3_34_step3 a b c e f ABC EF BC (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.opposingSides f BC; assumption)) (by euclid_assumption "" (show BC.intersectsCircle ABC; assumption)) (by euclid_assumption "some straight-line $EF$ touches the circle $ABC$" (show b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC; assumption)) (by euclid_assumption "$BC$ has been drawn across (the circle) from the point of contact $B$" (show b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c; assumption)))

  euclid_sentence "3.34.4"
    "But, $FBC$ is equal to $D$."
    (step4 : ∠ f:b:c = ∠ d1:d:d2) := by euclid_apply (helper_3_34_step4 b c f d1 d d2 (by euclid_assumption "" (show ∠ f:b:c = ∠ d1:d:d2; assumption)))

  euclid_sentence "3.34.5"
    "Thus, the (angle) in the segment $BAC$ is also equal to [angle] $D$."
    (step5 : ∠ b:a:c = ∠ d1:d:d2) := by euclid_apply (helper_3_34_step5 a b c f d1 d d2 (by euclid_assumption "" (show ∠ f:b:c = ∠ b:a:c; assumption)) (by euclid_assumption "" (show ∠ f:b:c = ∠ d1:d:d2; assumption)))

  refine ⟨b, c, hb_ABC, hc_ABC, hbc_ne, ?_⟩
  exact ⟨a, ha_ABC, step5⟩
  euclid_conclude_sentence "3.34.6"
    "Thus, the segment $BAC$, accepting an angle equal to the given rectilinear angle $D$, has been cut off from the given circle $ABC$. (Which is) the very thing it was required to do."

end Elements.Book3
