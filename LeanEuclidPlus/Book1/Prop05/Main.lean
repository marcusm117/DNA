import SystemE
import Book.Prop03
import Book.Prop04
import Mathlib.Tactic.Linarith
import Book1.Prop05.step1
import Book1.Prop05.step2
import Book1.Prop05.step3
import Book1.Prop05.step4
import Book1.Prop05.step5
import Book1.Prop05.step6
import Book1.Prop05.step7
import Book1.Prop05.step8
import Book1.Prop05.step9
import Book1.Prop05.step10
import Book1.Prop05.step11
import Book1.Prop05.step12
import Book1.Prop05.step13
import Book1.Prop05.step14
import Book1.Prop05.step15
import Book1.Prop05.step16
import Book1.Prop05.step17
import Book1.Prop05.step18
import Book1.Prop05.step19
import Book1.Prop05.step20
import Book1.Prop05.step21
import Book1.Prop05.step22
import Book1.Prop05.step23
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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
    (step1 : between b f d) := by euclid_apply (helper_1_5_step1 b f d (by euclid_assumption "" (show between b f d; assumption)))

  -- Cut G on AE with AG = AF (Prop.~1.3).
  euclid_apply (proposition_3 a e f a AC AB) as g
  euclid_sentence "1.5.2"
    "and let $AG$ have been cut off from the greater $AE$, equal to the lesser $AF$ [Prop.~1.3]."
    (step2 : between a g e ∧ |(a─g)| = |(a─f)|) := by euclid_apply (helper_1_5_step2 a e f g (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show |(a─g)| = |(f─a)|; assumption)))

  euclid_apply (line_from_points c f) as FC
  euclid_apply (line_from_points b g) as GB
  euclid_sentence "1.5.3"
    "Also, let the straight-lines $FC$ and $GB$ have been joined [Post.~1]. "
    (step3 : c.onLine FC ∧ f.onLine FC ∧ b.onLine GB ∧ g.onLine GB) := by euclid_apply (helper_1_5_step3 c f b g FC GB (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)))

  -- @assumption ("$AF$ is equal to $AG$", |(a─f)| = |(a─g)|)
  -- @assumption ("$AB$ to $AC$", |(a─b)| = |(a─c)|)
  -- The two "since" facts (AF=AG, AB=AC) assembled into the paired "two sides = two sides" form.
  euclid_sentence "1.5.4"
    "In fact, since $AF$ is equal to $AG$, and $AB$ to $AC$, the two (straight-lines) $FA$, $AC$ are equal to the two (straight-lines) $GA$, $AB$, respectively."
    (step4 : (|(f─a)| = |(g─a)|) ∧ (|(a─c)| = |(a─b)|)) := by euclid_apply (helper_1_5_step4 a b c f g (by euclid_assumption "" (show |(a─g)| = |(a─f)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─c)|; assumption)))

  -- The common angle FAG: it is the vertex-A angle of BOTH triangles (∠FAC and ∠GAB each = ∠FAG).
  euclid_sentence "1.5.5"
    "They also encompass a common angle, $FAG$."
    (step5 : (∠ f:a:c = ∠ f:a:g) ∧ (∠ g:a:b = ∠ f:a:g)) := by euclid_apply (helper_1_5_step5 a b c d e f g AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)))

  euclid_sentence "1.5.6"
    "Thus, the base $FC$ is equal to the base $GB$,"
    (step6 : |(f─c)| = |(g─b)|) := by euclid_apply (helper_1_5_step6 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)))

  -- "triangle AFC = triangle AGB": equal FIGURES, i.e. equal area (base is 1.5.6, angles are 1.5.8).
  euclid_sentence "1.5.7"
    "and the triangle $AFC$ will be equal to the triangle $AGB$,"
    (step7 : Triangle.area △ a:f:c = Triangle.area △ a:g:b) := by euclid_apply (helper_1_5_step7 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)) (by euclid_assumption "" (show |(f─c)| = |(g─b)|; assumption)))

  euclid_sentence "1.5.8"
    "and the remaining angles subtendend by the equal sides will be equal to the corresponding  remaining angles [Prop.~1.4]. "
    (step8 : (∠ a:c:f = ∠ a:b:g) ∧ (∠ a:f:c = ∠ a:g:b)) := by euclid_apply (helper_1_5_step8 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)))

  euclid_sentence "1.5.9"
    "(That is) $ACF$ to $ABG$,"
    (step9 : ∠ a:c:f = ∠ a:b:g) := by euclid_apply (helper_1_5_step9 a b c f g (by euclid_assumption "" (show ∠a:c:f = ∠a:b:g ∧ ∠a:f:c = ∠a:g:b; assumption)))

  euclid_sentence "1.5.10"
    "and $AFC$ to $AGB$."
    (step10 : ∠ a:f:c = ∠ a:g:b) := by euclid_apply (helper_1_5_step10 a b c f g (by euclid_assumption "" (show ∠a:c:f = ∠a:b:g ∧ ∠a:f:c = ∠a:g:b; assumption)))

  -- @assumption_valid
  have step11_assumption1 : |(a─f)| = |(a─g)| := by linarith
  -- @assumption_valid
  have step11_assumption2 : |(a─b)| = |(a─c)| := by assumption
  -- @assumption ("the whole of $AF$ is equal to the whole of $AG$", |(a─f)| = |(a─g)|)
  -- @assumption ("$AB$ is equal to $AC$", |(a─b)| = |(a─c)|)
  euclid_sentence "1.5.11"
    "And since the whole of $AF$ is equal to the whole of $AG$, within which $AB$ is equal to $AC$, the remainder $BF$ is thus equal to the remainder $CG$ [C.N.~3]."
    (step11 : |(b─f)| = |(c─g)|) := by euclid_apply (helper_1_5_step11 a b c d e f g AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "the whole of $AF$ is equal to the whole of $AG$" (show |(a─f)| = |(a─g)|; assumption)) (by euclid_assumption "$AB$ is equal to $AC$" (show |(a─b)| = |(a─c)|; assumption)))

  euclid_sentence "1.5.12"
    "But $FC$ was also shown (to be) equal to $GB$."
    (step12 : |(f─c)| = |(g─b)|) := by euclid_apply (helper_1_5_step12 f c g b (by euclid_assumption "" (show |(f─c)| = |(g─b)|; assumption)))

  -- The paired sides BF,FC = CG,GB (recalling steps 11 and 12/6).
  euclid_sentence "1.5.13"
    "So the two (straight-lines) $BF$, $FC$ are equal to the two (straight-lines) $CG$, $GB$, respectively,"
    (step13 : (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|)) := by euclid_apply (helper_1_5_step13 b c f g (by euclid_assumption "" (show |(b─f)| = |(c─g)|; assumption)) (by euclid_assumption "" (show |(f─c)| = |(g─b)|; assumption)))

  euclid_sentence "1.5.14"
    "and the angle $BFC$ (is) equal to the angle $CGB$,"
    (step14 : ∠ b:f:c = ∠ c:g:b) := by euclid_apply (helper_1_5_step14 a b c d e f g AB AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show |(a─f)| = |(a─g)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠a:f:c = ∠a:g:b; assumption)))

  -- The base BC is the common side of both triangles BFC and CGB (the segment b–c on line BC).
  euclid_sentence "1.5.15"
    "and the base $BC$ is common to them."
    (step15 : distinctPointsOnLine b c BC) := by euclid_apply (helper_1_5_step15 a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))

  -- "triangle BFC = triangle CGB": equal FIGURES, i.e. equal area (angles are 1.5.17).
  euclid_sentence "1.5.16"
    "Thus, the triangle $BFC$ will be equal to the triangle $CGB$,"
    (step16 : Triangle.area △ b:f:c = Triangle.area △ c:g:b) := by euclid_apply (helper_1_5_step16 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|); assumption)) (by euclid_assumption "" (show ∠b:f:c = ∠c:g:b; assumption)))

  euclid_sentence "1.5.17"
    "and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles [Prop.~1.4]."
    (step17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c)) := by euclid_apply (helper_1_5_step17 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|); assumption)) (by euclid_assumption "" (show ∠b:f:c = ∠c:g:b; assumption)))

  euclid_sentence "1.5.18"
    "Thus, $FBC$ is equal to $GCB$,"
    (step18 : ∠ f:b:c = ∠ g:c:b) := by euclid_apply (helper_1_5_step18 b c f g (by euclid_assumption "" (show (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c); assumption)))

  euclid_sentence "1.5.19"
    "and $BCF$ to $CBG$."
    (step19 : ∠ b:c:f = ∠ c:b:g) := by euclid_apply (helper_1_5_step19 a b c d e f g AB AC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b c BC; assumption)) (by euclid_assumption "" (show (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c); assumption)))

  -- @assumption_valid
  have step20_assumption1 : ∠ a:b:g = ∠ a:c:f := by linarith
  -- @assumption_valid
  have step20_assumption2 : ∠ c:b:g = ∠ b:c:f := by linarith
  -- @assumption ("the whole angle $ABG$ was shown (to be) equal to the whole angle $ACF$", ∠ a:b:g = ∠ a:c:f)
  -- @assumption ("$CBG$ is equal to $BCF$", ∠ c:b:g = ∠ b:c:f)
  euclid_sentence "1.5.20"
    "Therefore, since the whole angle $ABG$ was shown (to be) equal to the whole angle $ACF$, within which $CBG$ is equal to $BCF$, the remainder $ABC$ is thus equal to the remainder $ACB$ [C.N.~3]."
    (step20 : ∠ a:b:c = ∠ a:c:b) := by euclid_apply (helper_1_5_step20 a b c d e f g AB BC AC FC GB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine GB; assumption)) (by euclid_assumption "" (show g.onLine GB; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "the whole angle $ABG$ was shown (to be) equal to the whole angle $ACF$" (show ∠ a:b:g = ∠ a:c:f; assumption)) (by euclid_assumption "$CBG$ is equal to $BCF$" (show ∠ c:b:g = ∠ b:c:f; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─g)|; assumption)) (by euclid_assumption "" (show |(a─f)| = |(a─g)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─c)|; assumption)))

  -- "at the base": ABC, ACB already ARE the base angles (no conversion) → conclusion 1, = step20.
  euclid_sentence "1.5.21"
    "And they are at the base of triangle $ABC$."
    (step21 : ∠ a:b:c = ∠ a:c:b) := by euclid_apply (helper_1_5_step21 a b c (by euclid_assumption "" (show ∠ a:b:c = ∠ a:c:b; assumption)))

  euclid_sentence "1.5.22"
    "And $FBC$ was also shown (to be) equal to $GCB$."
    (step22 : ∠ f:b:c = ∠ g:c:b) := by euclid_apply (helper_1_5_step22 b c f g (by euclid_assumption "" (show ∠ f:b:c = ∠ g:c:b; assumption)))

  -- "under the base": FBC, GCB ARE the under-base angles CBD, BCE (via F on BD, G on CE).
  euclid_sentence "1.5.23"
    "And they are under the base. "
    (step23 : (∠ f:b:c = ∠ c:b:d) ∧ (∠ g:c:b = ∠ b:c:e)) := by euclid_apply (helper_1_5_step23 a b c d e f g AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine b c BC; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show between b f d; assumption)) (by euclid_assumption "" (show between a c e; assumption)) (by euclid_assumption "" (show between a g e; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─g)|; assumption)) (by euclid_assumption "" (show |(a─f)| = |(a─g)|; assumption)) (by euclid_assumption "" (show |(a─b)| = |(a─c)|; assumption)))

  -- conclusion 1 is step21; conclusion 2 = ∠CBD = ∠FBC = ∠GCB = ∠BCE (step23 identifies, step22 equates).
  exact ⟨step21, step23.1.symm.trans (step22.trans step23.2)⟩
  euclid_conclude_sentence "1.5.24"
    "Thus, for isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
