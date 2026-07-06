import SystemE

namespace Elements.Book3

-- orchestrator-agreed: tangent + ⟂ at contact ⟹ center on that ⟂ line (∀ o isCentre → o.onLine CA). Matches enunciation.
theorem proposition_19 : ∀ (a c e : Point) (ABC : Circle) (DE CA : Line),
  c.onLine DE ∧ c.onCircle ABC ∧ ¬ DE.intersectsCircle ABC ∧
  a.onLine CA ∧ c.onLine CA ∧ a ≠ c ∧
  e.onLine DE ∧ e ≠ c ∧ ∠ a:c:e = ∟ →
  ∀ o : Point, o.isCentre ABC → o.onLine CA :=
by
  sorry
