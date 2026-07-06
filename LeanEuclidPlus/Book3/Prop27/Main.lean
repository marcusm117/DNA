import SystemE

namespace Elements.Book3

-- III.27 (converse of III.26): In equal circles, angles standing on equal arcs are equal,
-- whether at the centers or at the circumferences.
-- Equal circles (equal radii |(g─b)|=|(h─e)|) + equal arcs (∠b:g:c=∠e:h:f as central angles)
-- ⟹ inscribed angles equal: ∠b:a:c=∠e:d:f.
-- The central-angle equality IS the arc hypothesis in our encoding, so restating it in the goal
-- would be circular; the genuine non-trivial conclusion is the inscribed-angle equality alone.
-- Proof sketch: reductio (if ∠BGC≠∠EHF, construct ∠BGK=∠EHF [I.23]; arc BK=arc EF [III.26];
-- but arc EF=arc BC, so BK=BC, lesser=greater, absurd); then ∠BAC=½∠BGC=½∠EHF=∠EDF [III.20].
theorem proposition_27 : ∀ (a b c d e f g h : Point) (BC EF : Line) (ABC DEF : Circle),
  g.isCentre ABC ∧ h.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  a.onCircle ABC ∧ d.onCircle DEF ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  a ≠ b ∧ a ≠ c ∧ d ≠ e ∧ d ≠ f ∧
  a.sameSide g BC ∧ d.sameSide h EF ∧
  |(g─b)| = |(h─e)| ∧
  ∠ b:g:c = ∠ e:h:f →
  ∠ b:a:c = ∠ e:d:f :=
by
  sorry
