import SystemE

namespace Elements.Book3

-- orchestrator-agreed (w/ note): internal touch = common pt a + ¬intersect + inner-center g inside ABC; goal `between f g a`
-- (F—G—A). Internal-vs-external disambiguation via g.insideCircle ABC is a modeling choice — flagged for a look.
theorem proposition_11 : ∀ (a f g : Point) (ABC ADE : Circle),
  a.onCircle ABC ∧ a.onCircle ADE ∧
  ¬ ABC.intersectsCircle ADE ∧
  g.insideCircle ABC ∧
  f.isCentre ABC ∧ g.isCentre ADE ∧
  f ≠ g →
  between f g a :=
by
  sorry
