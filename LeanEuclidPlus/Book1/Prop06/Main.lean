import SystemE
import Book.Prop03
import Book.Prop04
import Book1.Prop06.step1
import Book1.Prop06.step2
import Book1.Prop06.step3
import Book1.Prop06.step4
import Book1.Prop06.step5
import Book1.Prop06.step6
import Book1.Prop06.step7
import Book1.Prop06.step8
import Book1.Prop06.step9
import Book1.Prop06.step10
import Book1.Prop06.step11
import Book1.Prop06.sym
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| := by
  euclid_intros
  euclid_intro_sentence "1.6.0"
    "If a triangle has two angles equal to one another then the sides subtending the equal angles will also be equal to one another. Let $ABC$ be a triangle having the angle $ABC$ equal to the angle $ACB$. I say that side $AB$ is also equal to side $AC$. "
  -- Euclid argues by contradiction: suppose AB ≠ AC; each case is absurd.
  have habsurd : ¬ (|(a─b)| ≠ |(a─c)|) := by
    intro hne
    -- @assumption ("$AB$ is unequal to $AC$", |(a─b)| ≠ |(a─c)|)
    euclid_sentence "1.6.1"
      "For if $AB$ is unequal to $AC$ then one of them is greater."
      (step1 : |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)|) := by euclid_apply (helper_1_6_step1 a b c (by euclid_assumption "$AB$ is unequal to $AC$" (show |(a─b)| ≠ |(a─c)|; assumption)))
    by_cases hgt : |(a─b)| > |(a─c)|
    · -- Euclid's written case: let AB be the greater.
      euclid_sentence "1.6.2"
        "Let $AB$ be greater."
        (step2 : |(a─b)| > |(a─c)|) := by euclid_apply (helper_1_6_step2 a b c (by euclid_assumption "" (show |(a─b)| > |(a─c)|; assumption)))
      euclid_apply (proposition_3 b a a c AB AC) as d
      euclid_sentence "1.6.3"
        "And let $DB$, equal to the lesser $AC$, have been cut off from the greater $AB$ [Prop.~1.3]. "
        (step3 : between b d a ∧ |(b─d)| = |(a─c)|) := by euclid_apply (helper_1_6_step3 a b c d (by euclid_assumption "" (show between b d a; assumption)) (by euclid_assumption "" (show |(b─d)| = |(a─c)|; assumption)))
      euclid_apply (line_from_points d c) as DC
      euclid_sentence "1.6.4"
        "And let $DC$ have been joined [Post.~1]. "
        (step4 : d.onLine DC ∧ c.onLine DC) := by euclid_apply (helper_1_6_step4 d c DC (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)))
      euclid_sentence "1.6.5"
        "Therefore, since $DB$ is equal to $AC$, and $BC$ (is) common, the two sides $DB$, $BC$ are equal to the two sides $AC$, $CB$, respectively,"
        (step5 : |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)|) := by euclid_apply (helper_1_6_step5 a b c d (by euclid_assumption "" (show |(b─d)| = |(a─c)|; assumption)))
      euclid_sentence "1.6.6"
        "and the angle $DBC$ is equal to the angle $ACB$."
        (step6 : ∠ d:b:c = ∠ a:c:b) := by euclid_apply (helper_1_6_step6 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b d a; assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ a:c:b; assumption)))
      euclid_sentence "1.6.7"
        "Thus, the base $DC$ is equal to the base $AB$,"
        (step7 : |(d─c)| = |(a─b)|) := by euclid_apply (helper_1_6_step7 a b c d AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b d a; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show |(b─d)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠ d:b:c = ∠ a:c:b; assumption)))
      euclid_sentence "1.6.8"
        "and the triangle $DBC$ will be equal to the triangle $ACB$ [Prop.~1.4], the lesser to the greater."
        (step8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a)) := by euclid_apply (helper_1_6_step8 a b c d AB BC AC DC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b d a; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show |(b─d)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠ d:b:c = ∠ a:c:b; assumption)))
      euclid_sentence "1.6.9"
        "The very notion (is) absurd [C.N.~5]."
        (step9 : False) := by euclid_apply (helper_1_6_step9 a b c d AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show between b d a; assumption)) (by euclid_assumption "" (show |(b─d)| = |(a─c)|; assumption)) (by euclid_assumption "" (show ∠ d:b:c = ∠ a:c:b; assumption)) (by euclid_assumption "" (show |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a); assumption)))
      exact step9
    · -- the symmetric case (AC greater): the symmetric mirror, helper_1_6_sym.
      have hgt' : |(a─c)| > |(a─b)| := by
        rcases step1 with h | h
        · exact absurd h hgt
        · exact h
      have sym : False := by euclid_apply (helper_1_6_sym a b c AB BC AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ a:c:b; assumption)) (by euclid_assumption "" (show |(a─c)| > |(a─b)|; assumption)))
      exact sym
  euclid_sentence "1.6.10"
    "Thus, $AB$ is not unequal to $AC$."
    (step10 : ¬ (|(a─b)| ≠ |(a─c)|)) := by euclid_apply (helper_1_6_step10 a b c (by euclid_assumption "" (show ¬ (|(a─b)| ≠ |(a─c)|); assumption)))
  euclid_sentence "1.6.11"
    "Thus, (it is) equal. "
    (step11 : |(a─b)| = |(a─c)|) := by euclid_apply (helper_1_6_step11 a b c (by euclid_assumption "" (show ¬ (|(a─b)| ≠ |(a─c)|); assumption)))
  exact step11
  euclid_conclude_sentence "1.6.12"
    "Thus, if a triangle has two angles equal to one another then the sides subtending the equal angles will also be equal to one another. (Which is) the very thing it was required to show."

end Elements.Book1
