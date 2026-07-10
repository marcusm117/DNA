import SystemE
import Book1.Prop23.Main
import Book3.Prop32.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_34 : ∀ (ABC : Circle) (d1 d d2 : Point),
  d1 ≠ d ∧ d2 ≠ d →
  -- Non-degeneracy: the given angle must be a genuine (bent) rectilinear angle, strictly between
  -- zero and a straight angle. `d1 ≠ d ∧ d2 ≠ d` does NOT prevent d1,d,d2 being collinear (angle
  -- 0 or ∟+∟), and the cut-off (inscribed) angle ∠ b:a:c is always in (0, ∟+∟) — so a collinear
  -- given angle makes the ∃-conclusion FALSE (and collapses the chord onto the tangent line). (cf.
  -- Book1/Prop23's `formRectilinearAngle`, which admits and case-splits 0/straight; not usable here.)
  0 < ∠ d1:d:d2 → ∠ d1:d:d2 < ∟ + ∟ →
  ∃ (b c : Point), b.onCircle ABC ∧ c.onCircle ABC ∧ b ≠ c ∧
    ∃ a : Point, a.onCircle ABC ∧ ∠ b:a:c = ∠ d1:d:d2 :=
by
  euclid_intros
  euclid_intro_sentence "3.34.0"
    "To cut off a segment, accepting an angle equal to a given rectilinear angle, from a given circle. Let $ABC$ be the given circle, and $D$ the given rectilinear angle. So it is required to cut off a segment, accepting an angle equal to the given rectilinear angle $D$, from the given circle $ABC$."

  -- Get b on the circle ABC (tangent contact point)
  obtain ⟨b, hb_ABC⟩ := exists_point_on_circle ABC
  -- Get tangent line EF at b (Porism to III.16 — no explicit axiom; body sorry in Phase B)
  have hEF_exists : ∃ EF : Line, b.onLine EF ∧ ¬ EF.intersectsCircle ABC := by sorry
  obtain ⟨EF, hb_EF, hEF_notint⟩ := hEF_exists
  -- Get e and f on EF with b between them (needed for III.32 alternate-segment sides)
  have hef : ∃ e f : Point, e.onLine EF ∧ f.onLine EF ∧ between e b f := by sorry
  obtain ⟨e, f, he_EF, hf_EF, hbet_ebf⟩ := hef

  euclid_sentence "3.34.1"
    "Let $EF$ be drawn touching $ABC$ at point $B$.$^\\dag$"
    (step1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC) := by sorry

  -- Construction for step2: use Prop 1.23 to get direction point c₀ s.t. ∠c₀:b:f = ∠d1:d:d2
  have hc₀ : ∃ c₀ : Point, c₀ ≠ b ∧ ∠ c₀:b:f = ∠ d1:d:d2 := by sorry
  obtain ⟨c₀, hc₀ne, hc₀angle⟩ := hc₀
  -- Line BC through b and c₀ (the chord direction)
  have hbc₀ne : b ≠ c₀ := hc₀ne.symm
  euclid_apply (line_from_points b c₀) as BC
  -- Get c as the second intersection of BC with ABC (c is the chord endpoint on the circle)
  have hBC_int : BC.intersectsCircle ABC := by sorry
  obtain ⟨c, c', hc_ABC, hc_BC, hc'_ABC, hc'_BC, hcc'ne⟩ := intersections_circle_line ABC BC hBC_int

  euclid_sentence "3.34.2"
    "And let (angle) $FBC$, equal to angle $D$, be constructed on the straight-line $FB$, at the point $B$ on it [Prop.~1.23]."
    (step2 : ∠ f:b:c = ∠ d1:d:d2) := by sorry

  -- Get a in the alternate segment BAC (on ABC, opposite side of BC from f)
  have ha_exists : ∃ a : Point, a.onCircle ABC ∧ a.opposingSides f BC := by sorry
  obtain ⟨a, ha_ABC, ha_opp⟩ := ha_exists

  -- orchestrator-cite-fix: "[Prop.~1.32]" in the source text is a cite error; the alternate
  -- segment theorem is Euclid III.32, not I.32. Using proposition_32 from Book3.Prop32.Main.
  -- @assumption ("some straight-line $EF$ touches the circle $ABC$", b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC)
  -- @assumption ("$BC$ has been drawn across (the circle) from the point of contact $B$", b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c)
  euclid_sentence "3.34.3"
    "Therefore, since some straight-line $EF$ touches the circle $ABC$, and $BC$ has been drawn across (the circle) from the point of contact $B$, angle $FBC$ is thus equal to the angle constructed in the alternate segment $BAC$ [Prop.~1.32]."
    (step3 : ∠ f:b:c = ∠ b:a:c) := by sorry

  euclid_sentence "3.34.4"
    "But, $FBC$ is equal to $D$."
    (step4 : ∠ f:b:c = ∠ d1:d:d2) := by sorry

  euclid_sentence "3.34.5"
    "Thus, the (angle) in the segment $BAC$ is also equal to [angle] $D$."
    (step5 : ∠ b:a:c = ∠ d1:d:d2) := by sorry

  have hb_on : b.onCircle ABC := by sorry
  have hbc_ne : b ≠ c := by sorry
  refine ⟨b, c, hb_on, hc_ABC, hbc_ne, ?_⟩
  exact ⟨a, ha_ABC, step5⟩
  euclid_conclude_sentence "3.34.6"
    "Thus, the segment $BAC$, accepting an angle equal to the given rectilinear angle $D$, has been cut off from the given circle $ABC$. (Which is) the very thing it was required to do."

end Elements.Book3
