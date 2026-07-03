import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_12 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ ¬(c.onLine AB) →
  exists h : Point, h.onLine AB ∧ (∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) := by
  euclid_intros
  euclid_intro_sentence "1.12.0"
    "To draw a straight-line perpendicular to a given infinite straight-line from a given point which is not on it.   Let $AB$ be the given infinite straight-line  and $C$ the given point, which is not on ($AB$). So it is required to draw a  straight-line  perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on ($AB$). "

  have hd_ex : ∃ d : Point, d.opposingSides c AB := by sorry
  obtain ⟨d, hd⟩ := hd_ex
  euclid_sentence "1.12.1"
    "For let point $D$ have been taken at random on the other side (to $C$) of  the straight-line $AB$,"
    (step1 : d.opposingSides c AB) := by sorry

  have hEFG_ex : ∃ EFG : Circle, c.isCentre EFG ∧ d.onCircle EFG := by sorry
  obtain ⟨EFG, hcEFG, hdEFG⟩ := hEFG_ex
  have heg_ex : ∃ e g : Point, e.onLine AB ∧ g.onLine AB ∧ e ≠ g ∧ e.onCircle EFG ∧ g.onCircle EFG := by sorry
  obtain ⟨e, g, heAB, hgAB, heg, heEFG, hgEFG⟩ := heg_ex
  euclid_sentence "1.12.2"
    "and let the circle $EFG$ have been drawn with center $C$ and radius $CD$ [Post.~3],"
    (step2 : c.isCentre EFG ∧ d.onCircle EFG) := by sorry

  have hh_ex : ∃ h : Point, between e h g ∧ |(e─h)| = |(h─g)| := by sorry
  obtain ⟨h, hbetween, hlen⟩ := hh_ex
  euclid_sentence "1.12.3"
    "and let the straight-line $EG$ have been cut in half at (point) $H$ [Prop.~1.10],"
    (step3 : between e h g ∧ |(e─h)| = |(h─g)|) := by sorry

  have hCG_ex : ∃ CG : Line, c.onLine CG ∧ g.onLine CG := by sorry
  obtain ⟨CG, hCGc, hCGg⟩ := hCG_ex
  have hCH_ex : ∃ CH : Line, c.onLine CH ∧ h.onLine CH := by sorry
  obtain ⟨CH, hCHc, hCHh⟩ := hCH_ex
  have hCE_ex : ∃ CE : Line, c.onLine CE ∧ e.onLine CE := by sorry
  obtain ⟨CE, hCEc, hCEe⟩ := hCE_ex
  euclid_sentence "1.12.4"
    "and let the straight-lines $CG$, $CH$, and $CE$ have been joined."
    (step4 : distinctPointsOnLine c g CG ∧ distinctPointsOnLine c h CH ∧ distinctPointsOnLine c e CE) := by sorry

  euclid_wts "1.12.5"
    "I say that the  (straight-line) $CH$ has been drawn  perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on ($AB$). "

  -- @assumption_valid
  have step6_assumption1 : |(g─h)| = |(h─e)| := by euclid_finish
  -- @assumption_valid
  have step6_assumption2 : |(h─c)| = |(h─c)| := by rfl
  -- @assumption ("$GH$ is equal to $HE$", |(g─h)| = |(h─e)|)
  -- @assumption ("$HC$ (is) common", |(h─c)| = |(h─c)|)
  euclid_sentence "1.12.6"
    "For since $GH$ is equal to $HE$, and $HC$ (is) common, the two (straight-lines) $GH$,  $HC$ are equal to the two (straight-lines) $EH$, $HC$, respectively,"
    (step6 : |(g─h)| = |(e─h)| ∧ |(h─c)| = |(h─c)|) := by sorry

  euclid_sentence "1.12.7"
    "and the base $CG$ is equal to the base $CE$."
    (step7 : |(c─g)| = |(c─e)|) := by sorry

  euclid_sentence "1.12.8"
    "Thus, the angle $CHG$ is equal to the angle $EHC$ [Prop.~1.8],"
    (step8 : ∠ c:h:g = ∠ e:h:c) := by sorry

  euclid_sentence "1.12.9"
    "and they are adjacent."
    (step9 : h.onLine AB) := by sorry

  -- @assumption_valid
  have step10_assumption1 : ∠ c:h:g = ∠ e:h:c := by assumption
  -- @assumption ("the adjacent angles equal to one another", ∠ c:h:g = ∠ e:h:c)
  euclid_sentence "1.12.10"
    "But when a straight-line stood on a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle,"
    (step10 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) := by sorry

  euclid_sentence "1.12.11"
    "and the former straight-line is called a perpendicular to that upon which it stands [Def.~1.10]. "
    (step11 : ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟) := by sorry

  exact ⟨h, step9, step11⟩
  euclid_conclude_sentence "1.12.12"
    "Thus, the (straight-line) $CH$ has been drawn perpendicular to the given infinite straight-line $AB$ from the given point $C$, which is not on  ($AB$). (Which is) the very thing it was required to do."

end Elements.Book1
