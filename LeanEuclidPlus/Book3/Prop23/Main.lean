import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_23 : ∀ (a b c d : Point) (AB : Line) (ACB ADB : Circle),
  distinctPointsOnLine a b AB ∧
  a.onCircle ACB ∧ b.onCircle ACB ∧ c.onCircle ACB ∧
  a.onCircle ADB ∧ b.onCircle ADB ∧ d.onCircle ADB ∧
  c.sameSide d AB ∧
  between a c d ∧
  ∠ a:c:b = ∠ a:d:b ∧
  ACB ≠ ADB →
  False :=
by
  euclid_intros
  euclid_intro_sentence "3.23.0"
    "Two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line."

  -- orchestrator-restatement-of-givens: goal is False; euclid_intros already introduced the
  -- reductio hypotheses; step1 names the supposition (cf. Prop07 step1/2 pattern)
  euclid_sentence "3.23.1"
    "For, if possible, let the two similar and unequal segments of circles, $ACB$ and $ADB$, be constructed on the same side of the same straight-line $AB$."
    (step1 : c.sameSide d AB ∧ ACB ≠ ADB ∧ ∠ a:c:b = ∠ a:d:b) := by sorry

  euclid_apply (line_from_points a d) as ACD
  euclid_sentence "3.23.2"
    "And let $ACD$ be drawn through (the segments),"
    (step2 : a.onLine ACD ∧ c.onLine ACD ∧ d.onLine ACD) := by sorry

  euclid_apply (line_from_points c b) as CB
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.23.3"
    "and let $CB$ and $DB$ be joined."
    (step3 : distinctPointsOnLine c b CB ∧ distinctPointsOnLine d b DB) := by sorry

  -- @assumption ("segment $ACB$ is similar to segment $ADB$", ∠ a:c:b = ∠ a:d:b)
  -- orchestrator-restatement-of-hyp: similarity via Def.3.11 = equal inscribed angles;
  -- ∠ a:c:b = ∠ a:d:b is both the formalization of "ACB similar to ADB" and a theorem hyp;
  -- Def.3.11 is a definitional principle, not a separate Lean term, so its @assumption is dropped
  euclid_sentence "3.23.4"
    "Therefore, since segment $ACB$ is similar to segment $ADB$, and similar segments of circles are those accepting equal angles [Def.~3.11], angle $ACB$ is thus equal to $ADB$, the external to the internal."
    (step4 : ∠ a:c:b = ∠ a:d:b) := by sorry

  euclid_sentence "3.23.5"
    "The very thing is impossible [Prop.~1.16]."
    (step5 : False) := by sorry

  exact step5

  euclid_conclude_sentence "3.23.6"
    "Thus, two similar and unequal segments of circles cannot be constructed on the same side of the same straight-line."

end Elements.Book3
