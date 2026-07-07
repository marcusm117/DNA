import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
-- import Book3.Prop28.Main  -- orchestrator-note: Prop28 not yet mapped; needed for Phase B step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_30 : ∀ (a b o : Point) (ADB : Circle),
  a.onCircle ADB ∧ b.onCircle ADB ∧ a ≠ b ∧ o.isCentre ADB →
  ∃ d : Point, d.onCircle ADB ∧ ∠ a:o:d = ∠ d:o:b :=
by
  euclid_intros
  euclid_intro_sentence "3.30.0"
    "To cut a given circumference in half. Let $ADB$ be the given circumference. So it is required to cut circumference $ADB$ in half."

  euclid_apply (line_from_points a b) as AB
  euclid_sentence "3.30.1"
    "Let $AB$ be joined,"
    (step1 : distinctPointsOnLine a b AB) := by sorry

  euclid_apply (proposition_10 a b AB) as c
  euclid_sentence "3.30.2"
    "and let it be cut in half at (point) $C$ [Prop.~1.10]."
    (step2 : between a c b ∧ |(a─c)| = |(c─b)|) := by sorry

  euclid_apply (proposition_11 a b c AB) as d0
  have hcd0ne : c ≠ d0 := by sorry
  euclid_apply (line_from_points c d0) as CD
  have hCD_int : CD.intersectsCircle ADB := by sorry
  obtain ⟨d, d', hd_on, hd_onCD, hd'_on, hd'_onCD, hdd'ne⟩ := intersections_circle_line ADB CD hCD_int
  euclid_sentence "3.30.3"
    "And let $CD$ be drawn from point $C$, at right-angles to $AB$ [Prop.~1.11]."
    (step3 : ¬(d.onLine AB) ∧ ∠ a:c:d = ∟) := by sorry

  have hadne : a ≠ d := by sorry
  euclid_apply (line_from_points a d) as AD
  have hdbne : d ≠ b := by sorry
  euclid_apply (line_from_points d b) as DB
  euclid_sentence "3.30.4"
    "And let $AD$, and $DB$ be joined."
    (step4 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine d b DB) := by sorry

  -- @assumption ("$AC$ is equal to $CB$", |(a─c)| = |(c─b)|)
  -- @assumption ("$CD$ (is) common", |(c─d)| = |(c─d)|)
  euclid_sentence "3.30.5"
    "And since $AC$ is equal to $CB$, and $CD$ (is) common, the two (straight-lines) $AC$, $CD$ are equal to the two (straight-lines) $BC$, $CD$ (respectively)."
    (step5 : |(a─c)| = |(b─c)| ∧ |(c─d)| = |(c─d)|) := by sorry

  -- @assumption ("For (they are) each right-angles.", ∠ a:c:d = ∟ ∧ ∠ b:c:d = ∟)
  euclid_sentence "3.30.6"
    "And angle $ACD$ (is) equal to angle $BCD$. For (they are) each right-angles."
    (step6 : ∠ a:c:d = ∠ b:c:d) := by sorry

  euclid_sentence "3.30.7"
    "Thus, the base $AD$ is equal to the base $DB$ [Prop.~1.4]."
    (step7 : |(a─d)| = |(d─b)|) := by sorry

  euclid_sentence "3.30.8"
    "And equal straight-lines cut off equal circumferences, the greater (circumference being equal) to the greater, and the lesser to the lesser [Prop.~1.28]."
    (step8 : ∠ a:o:d = ∠ d:o:b) := by sorry

  euclid_sentence "3.30.9"
    "And the circumferences $AD$ and $DB$ are each less than a semi-circle."
    (step9 : ∠ a:o:d < ∟ + ∟ ∧ ∠ d:o:b < ∟ + ∟) := by sorry

  euclid_sentence "3.30.10"
    "Thus, circumference $AD$ (is) equal to circumference $DB$."
    (step10 : ∠ a:o:d = ∠ d:o:b) := by sorry

  exact ⟨d, hd_on, step10⟩
  euclid_conclude_sentence "3.30.11"
    "Thus, the given circumference has been cut in half at point $D$. (Which is) the very thing it was required to do."

end Elements.Book3
