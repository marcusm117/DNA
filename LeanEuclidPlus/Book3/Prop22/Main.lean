import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_22 : ∀ (a b c d : Point) (ABCD : Circle) (AC BD : Line),
  a.onCircle ABCD ∧ b.onCircle ABCD ∧ c.onCircle ABCD ∧ d.onCircle ABCD ∧
  distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD ∧
  b.opposingSides d AC ∧ a.opposingSides c BD →
  (∠ d:a:b + ∠ b:c:d = ∟ + ∟) ∧ (∠ a:b:c + ∠ c:d:a = ∟ + ∟) :=
by
  euclid_intros
  euclid_intro_sentence "3.22.0"
    "For quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles. Let $ABCD$ be a circle, and let $ABCD$ be a quadrilateral within it. I say that the (sum of the) opposite angles is equal to two right-angles."

  -- orchestrator-note: AC and BD are universal params in signature; construction claim = the joining facts already in scope
  euclid_sentence "3.22.1"
    "Let $AC$ and $BD$ be joined."
    (step1 : distinctPointsOnLine a c AC ∧ distinctPointsOnLine b d BD) := by sorry

  -- @assumption ("the three angles of any triangle are equal to two right-angles", ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)
  euclid_sentence "3.22.2"
    "Therefore, since the three angles of any triangle are equal to two right-angles [Prop.~1.32], the three angles $CAB$, $ABC$, and $BCA$ of triangle $ABC$ are thus equal to two right-angles."
    (step2 : ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟) := by sorry

  -- @assumption ("they are in the same segment $BADC$", ∃ (BC : Line), distinctPointsOnLine b c BC ∧ a.sameSide d BC)
  euclid_sentence "3.22.3"
    "And $CAB$ (is) equal to $BDC$. For they are in the same segment $BADC$ [Prop.~3.21]."
    (step3 : ∠ c:a:b = ∠ b:d:c) := by sorry

  -- @assumption ("they are in the same segment $ADCB$", ∃ (AB₀ : Line), distinctPointsOnLine a b AB₀ ∧ c.sameSide d AB₀)
  euclid_sentence "3.22.4"
    "And $ACB$ (is equal) to $ADB$. For they are in the same segment $ADCB$ [Prop.~3.21]."
    (step4 : ∠ a:c:b = ∠ a:d:b) := by sorry

  euclid_sentence "3.22.5"
    "Thus, the whole of $ADC$ is equal to $BAC$ and $ACB$."
    (step5 : ∠ a:d:c = ∠ b:a:c + ∠ a:c:b) := by sorry

  -- orchestrator-note: C.N.2 "added to both" — claim is the resulting sum-equality from adding ∠ABC to both sides of step5
  euclid_sentence "3.22.6"
    "Let $ABC$ be added to both."
    (step6 : ∠ a:b:c + ∠ a:d:c = ∠ a:b:c + ∠ b:a:c + ∠ a:c:b) := by sorry

  euclid_sentence "3.22.7"
    "Thus, $ABC$, $BAC$, and $ACB$ are equal to $ABC$ and $ADC$."
    (step7 : ∠ a:b:c + ∠ b:a:c + ∠ a:c:b = ∠ a:b:c + ∠ a:d:c) := by sorry

  -- @assumption ("$ABC$, $BAC$, and $ACB$ are equal to two right-angles", ∠ c:a:b + ∠ a:b:c + ∠ b:c:a = ∟ + ∟)
  -- orchestrator-note: ∠c:d:a = ∠ADC (vertex d, rays toward c and a); notation matches goal's second conjunct
  euclid_sentence "3.22.8"
    "But, $ABC$, $BAC$, and $ACB$ are equal to two right-angles. Thus, $ABC$ and $ADC$ are also equal to two right-angles."
    (step8 : ∠ a:b:c + ∠ c:d:a = ∟ + ∟) := by sorry

  -- orchestrator-note: ∠d:a:b = ∠BAD (vertex a, rays toward d and b); ∠b:c:d = ∠DCB (vertex c, rays toward b and d); notation matches goal's first conjunct
  euclid_sentence "3.22.9"
    "Similarly, we can show that angles $BAD$ and $DCB$ are also equal to two right-angles."
    (step9 : ∠ d:a:b + ∠ b:c:d = ∟ + ∟) := by sorry

  exact ⟨step9, step8⟩
  euclid_conclude_sentence "3.22.10"
    "Thus, for quadrilaterals within circles, the (sum of the) opposite angles is equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book3
