import SystemE
import Book.Prop11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
--mapdone
set_option systemE.solverTime 30 in
theorem proposition_13 : ∀ (a b c d : Point) (AB CD : Line),
  AB ≠ CD ∧ distinctPointsOnLine a b AB ∧ distinctPointsOnLine c d CD ∧ between d b c →
  ∠ c:b:a + ∠ a:b:d = ∟ + ∟ := by
  euclid_intros
  euclid_intro_sentence "1.13.0"
    "If a straight-line stood on a(nother)  straight-line makes angles, it will certainly either make two right-angles, or (angles whose sum is) equal to two right-angles. For  let some straight-line $AB$ stood on the straight-line $CD$ make the angles $CBA$ and $ABD$. I say that the angles $CBA$ and $ABD$ are certainly either two right-angles, or (have a sum) equal to two right-angles. "
  by_cases h_eq : ∠ c:b:a = ∠ a:b:d
  · -- @assumption ("$CBA$ is equal to $ABD$", ∠ c:b:a = ∠ a:b:d)
    euclid_sentence "1.13.1"
      "In fact, if $CBA$ is equal to $ABD$ then they are two right-angles [Def.~1.10]."
      (step1 : ∠ c:b:a = ∟ ∧ ∠ a:b:d = ∟) := by sorry
    obtain ⟨h1, h2⟩ := step1
    euclid_finish
  · euclid_apply (proposition_11 c d b CD) as e
    euclid_apply (line_from_points b e) as BE
    euclid_sentence "1.13.2"
      "But, if not, let $BE$ have been drawn from the point $B$ at right-angles to [the straight-line] $CD$ [Prop.~1.11]."
      (step2 : distinctPointsOnLine b e BE ∧ ∠ c:b:e = ∟) := by sorry
    euclid_sentence "1.13.3"
      "Thus, $CBE$ and $EBD$ are two right-angles."
      (step3 : ∠ c:b:e = ∟ ∧ ∠ e:b:d = ∟) := by sorry
    -- @assumption_gap
    have step4_assumption1 : ∠ c:b:e = ∠ c:b:a + ∠ a:b:e := by sorry
    -- @assumption ("$CBE$ is equal to the two (angles) $CBA$ and $ABE$", ∠ c:b:e = ∠ c:b:a + ∠ a:b:e)
    euclid_sentence "1.13.4"
      "And since $CBE$ is equal to the two (angles) $CBA$ and $ABE$, let $EBD$ have been added to both."
      (step4 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d) := by sorry
    euclid_sentence "1.13.5"
      "Thus, the (sum of the angles) $CBE$ and $EBD$ is equal to the  (sum of the) three (angles) $CBA$, $ABE$, and $EBD$ [C.N.~2]."
      (step5 : ∠ c:b:e + ∠ e:b:d = ∠ c:b:a + ∠ a:b:e + ∠ e:b:d) := by sorry
    -- @assumption_valid
    have step6_assumption1 : ∠ d:b:a = ∠ d:b:e + ∠ e:b:a := by euclid_finish
    -- @assumption ("$DBA$ is equal to the two (angles) $DBE$ and $EBA$", ∠ d:b:a = ∠ d:b:e + ∠ e:b:a)
    euclid_sentence "1.13.6"
      "Again, since $DBA$ is equal to the two (angles) $DBE$ and $EBA$, let $ABC$ have been added to both."
      (step6 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) := by sorry
    euclid_sentence "1.13.7"
      "Thus, the (sum of the angles) $DBA$ and $ABC$ is equal to the (sum of the) three (angles) $DBE$, $EBA$, and $ABC$ [C.N.~2]."
      (step7 : ∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) := by sorry
    euclid_sentence "1.13.8"
      "But (the sum of) $CBE$ and $EBD$ was also shown (to be) equal to the (sum of the) same three (angles)."
      (step8 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) := by sorry
    euclid_sentence "1.13.9"
      "And things equal to the same thing are also equal to one another [C.N.~1]."
      (step9 : (∠ c:b:e + ∠ e:b:d = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
               (∠ d:b:a + ∠ a:b:c = ∠ d:b:e + ∠ e:b:a + ∠ a:b:c) →
               (∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c)) := by sorry
    euclid_sentence "1.13.10"
      "Therefore,  (the sum of) $CBE$ and $EBD$ is also equal to (the sum of) $DBA$ and $ABC$."
      (step10 : ∠ c:b:e + ∠ e:b:d = ∠ d:b:a + ∠ a:b:c) := by sorry
    euclid_sentence "1.13.11"
      "But, (the sum of) $CBE$ and $EBD$ is two right-angles."
      (step11 : ∠ c:b:e + ∠ e:b:d = ∟ + ∟) := by sorry
    euclid_sentence "1.13.12"
      "Thus, (the sum of) $ABD$ and $ABC$ is also equal to two right-angles. "
      (step12 : ∠ c:b:a + ∠ a:b:d = ∟ + ∟) := by sorry
    exact step12
  euclid_conclude_sentence "1.13.13"
    "Thus, if a straight-line stood on a(nother)  straight-line makes angles, it will certainly either make two right-angles, or (angles whose sum is) equal to two right-angles. (Which is) the very thing it was required to show."

end Elements.Book1
