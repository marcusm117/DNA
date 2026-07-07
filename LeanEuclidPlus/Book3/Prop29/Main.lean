import SystemE
import Book3.Prop01.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem proposition_29 : ∀ (b c e f k l : Point) (ABC DEF : Circle),
  k.isCentre ABC ∧ l.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧
  e.onCircle DEF ∧ f.onCircle DEF ∧
  |(k─b)| = |(l─e)| ∧
  ∠ b:k:c = ∠ e:l:f →
  |(b─c)| = |(e─f)| :=
by
  euclid_intros
  euclid_intro_sentence "3.29.0"
    "In equal circles, equal straight-lines subtend equal circumferences. Let $ABC$ and $DEF$ be equal circles, and within them let the equal circumferences $BGC$ and $EHF$ be cut off. And let the straight-lines $BC$ and $EF$ be joined. I say that $BC$ is equal to $EF$."

  -- Faithful "find the centres [3.1]": construct the located centres k', l' via proposition_1, then
  -- identify them with the given centres k, l (centre_unique) — honors the III.1 construction.
  euclid_apply (proposition_1 ABC) as k'
  euclid_apply (proposition_1 DEF) as l'
  euclid_sentence "3.29.1"
    "For let the centers of the circles be found [Prop.~3.1], and let them be (at) $K$ and $L$."
    (step1 : k'.isCentre ABC ∧ k' = k ∧ l'.isCentre DEF ∧ l' = l) := by sorry

  euclid_apply (line_from_points b k) as BK
  euclid_apply (line_from_points k c) as KC
  euclid_apply (line_from_points e l) as EL
  euclid_apply (line_from_points l f) as LF
  euclid_sentence "3.29.2"
    "And let $BK$, $KC$, $EL$, and $LF$ be joined."
    (step2 : distinctPointsOnLine b k BK ∧ distinctPointsOnLine k c KC ∧ distinctPointsOnLine e l EL ∧ distinctPointsOnLine l f LF) := by sorry

  -- @assumption ("the circumference $BGC$ is equal to the circumference $EHF$", ∠ b:k:c = ∠ e:l:f)
  -- orchestrator-note: arc BGC = arc EHF is encoded as ∠b:k:c = ∠e:l:f (central-angle convention, primer §arc);
  -- assertion "angle BKC = ELF" is thus co-identified with the arc assumption in our encoding.
  euclid_sentence "3.29.3"
    "And since the circumference $BGC$ is equal to the circumference $EHF$, the angle $BKC$ is also equal to (angle) $ELF$ [Prop.~3.27]."
    (step3 : ∠ b:k:c = ∠ e:l:f) := by sorry

  -- @assumption ("the circles $ABC$ and $DEF$ are equal", |(k─b)| = |(l─e)|)
  euclid_sentence "3.29.4"
    "And since the circles $ABC$ and $DEF$ are equal, their radii are also equal [Def.~3.1]."
    (step4 : |(k─b)| = |(k─c)| ∧ |(l─e)| = |(l─f)|) := by sorry

  euclid_sentence "3.29.5"
    "So the two (straight-lines) $BK$, $KC$ are equal to the two (straight-lines) $EL$, $LF$ (respectively)."
    (step5 : |(k─b)| = |(l─e)| ∧ |(k─c)| = |(l─f)|) := by sorry

  -- orchestrator-note: "they contain equal angles" = the included angle ∠BKC = ∠ELF; co-identified with
  -- the hypothesis ∠b:k:c = ∠e:l:f (arc encoding); retained for faithful SAS-argument structure.
  euclid_sentence "3.29.6"
    "And they contain equal angles."
    (step6 : ∠ b:k:c = ∠ e:l:f) := by sorry

  euclid_sentence "3.29.7"
    "Thus, the base $BC$ is equal to the base $EF$ [Prop.~1.4]."
    (step7 : |(b─c)| = |(e─f)|) := by sorry

  exact step7
  euclid_conclude_sentence "3.29.8"
    "Thus, in equal circles, equal straight-lines subtend equal circumferences. (Which is) the very thing it was required to show."

end Elements.Book3
