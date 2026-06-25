import SystemE
import Book.Prop03
import Book.Prop04

namespace Elements.Book1

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| :=
by
  euclid_intros
  by_contra -- this contra method I would argue is not as faithful as the method I suggest.
  by_cases |(a─b)| > |(a─c)|-- where is the "For if $AB$ is unequal to $AC$". and the " one of them is greater"
  . euclid_apply (proposition_3 b a a c AB AC) as d -- "Let $AB$ be greater. And let $DB$, equal to the lesser $AC$, have been cut off from the greater $AB$ [Prop.~1.3] this is alright, but where is "$DB$, equal to the lesser $AC$,"
    euclid_apply (line_from_points d c) as DC -- "And let $DC$ have been joined", good.
    euclid_apply proposition_4 b d c c a b AB DC BC AC AB BC -- where is "the two sides $DB$, $BC$ are equal to the two sides $AC$, $CB$, respectively"
    euclid_finish -- where is "angle $DBC$ is equal to the angle $ACB$". where is "$DC$ is equal to the base $AB$".. where is " the triangle $DBC$ will be equal to the triangle $ACB$". also he says " The very notion (is) absurd [C.N.~5]" here at the end, NOT at the beginning through by_contra.
  . euclid_apply (proposition_3 c a a b AC AB) as d -- euclid did not write this case, and they do not explicitely say so in the proof.
    euclid_apply (line_from_points d b) as DB
    euclid_apply (proposition_4 c d b b a c AC DB BC AB AC BC)
    euclid_finish

end Elements.Book1
