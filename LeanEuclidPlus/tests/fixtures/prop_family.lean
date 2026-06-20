import SystemE

namespace Elements.Book1

theorem proposition_5 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(a─b)| = |(a─c)| →
  ∠ a:b:c = ∠ a:c:b :=
by
  euclid_intros
  euclid_finish

theorem proposition_5' : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ |(a─b)| = |(a─c)| →
  ∠ c:b:a = ∠ b:c:a :=
by
  euclid_intros
  euclid_apply (proposition_5 a b c AB BC AC)
  euclid_finish

end Elements.Book1
