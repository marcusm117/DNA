import SystemE
import Book.Prop03
import Book.Prop04
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "

  -- F is taken on BD (between B and D), short enough that AF can be cut off from AE.
  euclid_apply (point_between_points_shorter_than AB b d (c─e)) as f
  euclid_sentence "1.5.1"
    "For let the point $F$ have been taken at random on  $BD$,"
    (step1 : between b f d) := by sorry

  -- Cut G on AE with AG = AF (Prop.~1.3).
  euclid_apply (proposition_3 a e f a AC AB) as g
  euclid_sentence "1.5.2"
    "and let $AG$ have been cut off from the greater $AE$, equal to the lesser $AF$ [Prop.~1.3]."
    (step2 : between a g e ∧ |(a─g)| = |(a─f)|) := by sorry

  euclid_apply (line_from_points c f) as FC
  euclid_apply (line_from_points b g) as GB
  euclid_sentence "1.5.3"
    "Also, let the straight-lines $FC$ and $GB$ have been joined [Post.~1]. "
    (step3 : c.onLine FC ∧ f.onLine FC ∧ b.onLine GB ∧ g.onLine GB) := by sorry

  -- @assumption ("$AF$ is equal to $AG$", |(a─f)| = |(a─g)|)
  -- @assumption ("$AB$ to $AC$", |(a─b)| = |(a─c)|)
  -- The two "since" facts (AF=AG, AB=AC) assembled into the paired "two sides = two sides" form.
  euclid_sentence "1.5.4"
    "In fact, since $AF$ is equal to $AG$, and $AB$ to $AC$, the two (straight-lines) $FA$, $AC$ are equal to the two (straight-lines) $GA$, $AB$, respectively."
    (step4 : (|(f─a)| = |(g─a)|) ∧ (|(a─c)| = |(a─b)|)) := by sorry

  -- The common angle FAG: it is the vertex-A angle of BOTH triangles (∠FAC and ∠GAB each = ∠FAG).
  euclid_sentence "1.5.5"
    "They also encompass a common angle, $FAG$."
    (step5 : (∠ f:a:c = ∠ f:a:g) ∧ (∠ g:a:b = ∠ f:a:g)) := by sorry

  euclid_sentence "1.5.6"
    "Thus, the base $FC$ is equal to the base $GB$,"
    (step6 : |(f─c)| = |(g─b)|) := by sorry

  -- "triangle AFC = triangle AGB": equal FIGURES, i.e. equal area (base is 1.5.6, angles are 1.5.8).
  euclid_sentence "1.5.7"
    "and the triangle $AFC$ will be equal to the triangle $AGB$,"
    (step7 : Triangle.area △ a:f:c = Triangle.area △ a:g:b) := by sorry

  euclid_sentence "1.5.8"
    "and the remaining angles subtendend by the equal sides will be equal to the corresponding  remaining angles [Prop.~1.4]. "
    (step8 : (∠ a:c:f = ∠ a:b:g) ∧ (∠ a:f:c = ∠ a:g:b)) := by sorry

  euclid_sentence "1.5.9"
    "(That is) $ACF$ to $ABG$,"
    (step9 : ∠ a:c:f = ∠ a:b:g) := by sorry

  euclid_sentence "1.5.10"
    "and $AFC$ to $AGB$."
    (step10 : ∠ a:f:c = ∠ a:g:b) := by sorry

  -- @assumption_valid
  have step11_assumption1 : |(a─f)| = |(a─g)| := by linarith
  -- @assumption_valid
  have step11_assumption2 : |(a─b)| = |(a─c)| := by assumption
  -- @assumption ("the whole of $AF$ is equal to the whole of $AG$", |(a─f)| = |(a─g)|)
  -- @assumption ("$AB$ is equal to $AC$", |(a─b)| = |(a─c)|)
  euclid_sentence "1.5.11"
    "And since the whole of $AF$ is equal to the whole of $AG$, within which $AB$ is equal to $AC$, the remainder $BF$ is thus equal to the remainder $CG$ [C.N.~3]."
    (step11 : |(b─f)| = |(c─g)|) := by sorry

  euclid_sentence "1.5.12"
    "But $FC$ was also shown (to be) equal to $GB$."
    (step12 : |(f─c)| = |(g─b)|) := by sorry

  -- The paired sides BF,FC = CG,GB (recalling steps 11 and 12/6).
  euclid_sentence "1.5.13"
    "So the two (straight-lines) $BF$, $FC$ are equal to the two (straight-lines) $CG$, $GB$, respectively,"
    (step13 : (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|)) := by sorry

  euclid_sentence "1.5.14"
    "and the angle $BFC$ (is) equal to the angle $CGB$,"
    (step14 : ∠ b:f:c = ∠ c:g:b) := by sorry

  -- The base BC is the common side of both triangles BFC and CGB (the segment b–c on line BC).
  euclid_sentence "1.5.15"
    "and the base $BC$ is common to them."
    (step15 : distinctPointsOnLine b c BC) := by sorry

  -- "triangle BFC = triangle CGB": equal FIGURES, i.e. equal area (angles are 1.5.17).
  euclid_sentence "1.5.16"
    "Thus, the triangle $BFC$ will be equal to the triangle $CGB$,"
    (step16 : Triangle.area △ b:f:c = Triangle.area △ c:g:b) := by sorry

  euclid_sentence "1.5.17"
    "and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles [Prop.~1.4]."
    (step17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c)) := by sorry

  euclid_sentence "1.5.18"
    "Thus, $FBC$ is equal to $GCB$,"
    (step18 : ∠ f:b:c = ∠ g:c:b) := by sorry

  euclid_sentence "1.5.19"
    "and $BCF$ to $CBG$."
    (step19 : ∠ b:c:f = ∠ c:b:g) := by sorry

  -- @assumption_valid
  have step20_assumption1 : ∠ a:b:g = ∠ a:c:f := by linarith
  -- @assumption_valid
  have step20_assumption2 : ∠ c:b:g = ∠ b:c:f := by linarith
  -- @assumption ("the whole angle $ABG$ was shown (to be) equal to the whole angle $ACF$", ∠ a:b:g = ∠ a:c:f)
  -- @assumption ("$CBG$ is equal to $BCF$", ∠ c:b:g = ∠ b:c:f)
  euclid_sentence "1.5.20"
    "Therefore, since the whole angle $ABG$ was shown (to be) equal to the whole angle $ACF$, within which $CBG$ is equal to $BCF$, the remainder $ABC$ is thus equal to the remainder $ACB$ [C.N.~3]."
    (step20 : ∠ a:b:c = ∠ a:c:b) := by sorry

  -- "at the base": ABC, ACB already ARE the base angles (no conversion) → conclusion 1, = step20.
  euclid_sentence "1.5.21"
    "And they are at the base of triangle $ABC$."
    (step21 : ∠ a:b:c = ∠ a:c:b) := by sorry

  euclid_sentence "1.5.22"
    "And $FBC$ was also shown (to be) equal to $GCB$."
    (step22 : ∠ f:b:c = ∠ g:c:b) := by sorry

  -- "under the base": FBC, GCB ARE the under-base angles CBD, BCE (via F on BD, G on CE).
  euclid_sentence "1.5.23"
    "And they are under the base. "
    (step23 : (∠ f:b:c = ∠ c:b:d) ∧ (∠ g:c:b = ∠ b:c:e)) := by sorry

  -- conclusion 1 is step21; conclusion 2 = ∠CBD = ∠FBC = ∠GCB = ∠BCE (step23 identifies, step22 equates).
  exact ⟨step21, step23.1.symm.trans (step22.trans step23.2)⟩
  euclid_conclude_sentence "1.5.24"
    "Thus, for isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
