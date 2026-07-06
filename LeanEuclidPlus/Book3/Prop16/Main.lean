import SystemE

namespace Elements.Book3

-- Clause 3 (the horn/curvilinear-angle sentence: "the angle of the semi-circle is greater than
-- any acute rectilinear angle whatsoever, and the remaining angle is less") is OMITTED — curvilinear
-- angle magnitude has no rendering in System E.
-- orchestrator-agreed (horn omitted): clause 1 (⟂ at diameter-end touches circle) ∧ clause 2 (every OTHER line through a
-- cuts the circle). Clause 2 is FAITHFUL (not merely "stronger"): "no line interposed between tangent and arc" ⟺ "every
-- non-tangent line through a cuts" — a point on the circle admits only tangent-or-secant lines; this IS Euclid's gloss.
-- Horn clause 3 (curvilinear semicircle-angle magnitude) OMITTED — genuine expressibility gap, no E term for a curved angle.
theorem proposition_16 : ∀ (a b d e : Point) (ABC : Circle) (AE : Line),
    d.isCentre ABC ∧
    a.onCircle ABC ∧ b.onCircle ABC ∧ between a d b ∧
    distinctPointsOnLine a e AE ∧
    ∠ e:a:b = ∟ →
    ((∃ p : Point, p.onLine AE ∧ p.onCircle ABC) ∧ ¬ AE.intersectsCircle ABC) ∧
    (∀ (FA : Line), a.onLine FA → FA ≠ AE → FA.intersectsCircle ABC) :=
by
  sorry
