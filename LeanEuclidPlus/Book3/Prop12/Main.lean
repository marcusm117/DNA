import SystemE

namespace Elements.Book3

-- orchestrator-agreed (w/ note): external touch = common pt a + ¬intersect + each center outside the other; goal
-- `between f a g` (contact A between the two centers). External-disambiguation via outsideCircle is a modeling choice.
theorem proposition_12 : ∀ (a f g : Point) (ABC ADE : Circle),
  f.isCentre ABC ∧
  g.isCentre ADE ∧
  a.onCircle ABC ∧
  a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  f.outsideCircle ADE ∧
  g.outsideCircle ABC →
  between f a g :=
by
  sorry
