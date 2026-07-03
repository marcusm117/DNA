import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
--map done
set_option systemE.solverTime 30 in
theorem proposition_15 : ∀ (a b c d e : Point) (AB CD : Line),
  distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ e.onLine AB ∧ e.onLine CD ∧
  CD ≠ AB ∧ (between d e c) ∧ (between a e b) →
  (∠ a:e:c = ∠ d:e:b) ∧ (∠ c:e:b = ∠ a:e:d) := by
  euclid_intros
  euclid_intro_sentence "1.15.0"
    "If two straight-lines cut one another then they make the vertically opposite angles equal to one another.  For let the two straight-lines $AB$ and $CD$ cut one another at the point $E$. I say that  angle $AEC$ is equal to (angle) $DEB$, and (angle) $CEB$ to (angle) $AED$. "

  -- @assumption_valid
  have step1_assumption1 : between d e c := by assumption
  -- @assumption ("the straight-line $AE$ stands on the straight-line $CD$", between d e c)
  euclid_sentence "1.15.1"
    "For since the straight-line $AE$ stands on the straight-line $CD$, making the angles $CEA$ and $AED$, the (sum of the) angles $CEA$ and $AED$ is thus equal to two right-angles [Prop.~1.13]."
    (step1 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟) := by sorry

  -- @assumption_valid
  have step2_assumption1 : between a e b := by assumption
  -- @assumption ("the straight-line $DE$ stands on the straight-line $AB$, making the angles $AED$ and $DEB$", between a e b)
  euclid_sentence "1.15.2"
    "Again, since the straight-line $DE$ stands on the straight-line $AB$, making the angles $AED$ and $DEB$, the (sum of the) angles $AED$ and $DEB$ is thus equal to two right-angles [Prop.~1.13]."
    (step2 : ∠ a:e:d + ∠ d:e:b = ∟ + ∟) := by sorry

  euclid_sentence "1.15.3"
    "But (the sum of) $CEA$ and $AED$ was also shown (to be) equal to two right-angles."
    (step3 : ∠ c:e:a + ∠ a:e:d = ∟ + ∟) := by sorry

  euclid_sentence "1.15.4"
    "Thus, (the sum of) $CEA$ and $AED$ is equal to (the sum of) $AED$ and $DEB$ [C.N.~1]."
    (step4 : ∠ c:e:a + ∠ a:e:d = ∠ a:e:d + ∠ d:e:b) := by sorry

  euclid_sentence "1.15.5"
    "Let $AED$ have been subtracted from both."
    (step5 : ∠ c:e:a + ∠ a:e:d - ∠ a:e:d = ∠ a:e:d + ∠ d:e:b - ∠ a:e:d) := by sorry

  euclid_sentence "1.15.6"
    "Thus, the remainder $CEA$ is equal to the remainder $BED$ [C.N.~3]."
    (step6 : ∠ c:e:a = ∠ b:e:d) := by sorry

  euclid_sentence "1.15.7"
    "Similarly, it can be shown that $CEB$ and $DEA$ are also equal. "
    (step7 : ∠ c:e:b = ∠ d:e:a) := by sorry

  have h1 : ∠ a:e:c = ∠ d:e:b := by sorry
  have h2 : ∠ c:e:b = ∠ a:e:d := by sorry
  exact ⟨h1, h2⟩
  euclid_conclude_sentence "1.15.8"
    "Thus, if two straight-lines cut one another then they make the vertically opposite angles equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
