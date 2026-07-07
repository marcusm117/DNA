import SystemE
import Book1.Prop08.Main
import Book3.Prop01.Main
import Book3.Prop26.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_28 : ∀ (a b d e k l : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧
  k.isCentre ABC ∧ l.isCentre DEF ∧
  |(k─a)| = |(l─d)| ∧
  a ≠ b ∧ d ≠ e ∧
  |(a─b)| = |(d─e)| →
  ∠ a:k:b = ∠ d:l:e :=
by
  euclid_intros
  euclid_intro_sentence "3.28.0"
    "In equal circles, equal straight-lines cut off equal circumferences, the greater (circumference being equal) to the greater, and the lesser to the lesser. Let $ABC$ and $DEF$ be equal circles, and let $AB$ and $DE$ be equal straight-lines in these circles, cutting off the greater circumferences $ACB$ and $DFE$, and the lesser (circumferences) $AGB$ and $DHE$ (respectively). I say that the greater circumference $ACB$ is equal to the greater circumference $DFE$, and the lesser circumference $AGB$ to (the lesser) $DHE$."

  -- Faithful "find the centres [3.1]": construct the located centres k', l' via proposition_1, then
  -- identify them with the given centres k, l (centre_unique) — honors the III.1 construction.
  euclid_apply (proposition_1 ABC) as k'
  euclid_apply (proposition_1 DEF) as l'
  euclid_sentence "3.28.1"
    "For let the centers of the circles, $K$ and $L$, be found [Prop.~3.1],"
    (step1 : k'.isCentre ABC ∧ k' = k ∧ l'.isCentre DEF ∧ l' = l) := by sorry

  have hak : a ≠ k := by sorry
  have hkb : k ≠ b := by sorry
  have hdl : d ≠ l := by sorry
  have hle : l ≠ e := by sorry
  euclid_apply (line_from_points a k) as AK
  euclid_apply (line_from_points k b) as KB
  euclid_apply (line_from_points d l) as DL
  euclid_apply (line_from_points l e) as LE
  euclid_sentence "3.28.2"
    "and let $AK$, $KB$, $DL$, and $LE$ be joined."
    (step2 : distinctPointsOnLine a k AK ∧ distinctPointsOnLine k b KB ∧ distinctPointsOnLine d l DL ∧ distinctPointsOnLine l e LE) := by sorry

  -- @assumption ("($ABC$ and $DEF$) are equal circles", |(k─a)| = |(l─d)|)
  -- orchestrator-restatement-plus: first conjunct recaps hypothesis; second conjunct |(k─b)|=|(l─e)| is new (b on ABC, e on DEF, equal radii)
  euclid_sentence "3.28.3"
    "And since ($ABC$ and $DEF$) are equal circles, their radii are also equal [Def.~3.1]."
    (step3 : |(k─a)| = |(l─d)| ∧ |(k─b)| = |(l─e)|) := by sorry

  euclid_sentence "3.28.4"
    "So the two (straight-lines) $AK$, $KB$ are equal to the two (straight-lines) $DL$, $LE$ (respectively)."
    (step4 : |(a─k)| = |(d─l)| ∧ |(k─b)| = |(l─e)|) := by sorry

  -- orchestrator-restatement: recall of hypothesis |(a─b)|=|(d─e)| for SSS argument [1.8]
  euclid_sentence "3.28.5"
    "And the base $AB$ (is) equal to the base $DE$."
    (step5 : |(a─b)| = |(d─e)|) := by sorry

  euclid_sentence "3.28.6"
    "Thus, angle $AKB$ is equal to angle $DLE$ [Prop.~1.8]."
    (step6 : ∠ a:k:b = ∠ d:l:e) := by sorry

  -- @assumption ("equal angles stand upon equal circumferences, when they are at the centers", ∠ a:k:b = ∠ d:l:e)
  -- orchestrator-arc-convention: arc AGB=DHE rendered as central angle ∠a:k:b=∠d:l:e (arc := central angle, Primer §arc); same form as step6 (angle-equality ⟹ arc-equality is trivial in this encoding)
  euclid_sentence "3.28.7"
    "And equal angles stand upon equal circumferences, when they are at the centers [Prop.~3.26]. Thus, circumference $AGB$ (is) equal to $DHE$."
    (step7 : ∠ a:k:b = ∠ d:l:e) := by sorry

  -- orchestrator-vocab-limitation: "whole circle equal" = equal radii; no circumference-magnitude primitive in SystemE; |(k─a)|=|(l─d)| is the equal-circles condition
  euclid_sentence "3.28.8"
    "And the whole circle $ABC$ is also equal to the whole circle $DEF$."
    (step8 : |(k─a)| = |(l─d)|) := by sorry

  -- orchestrator-arc-convention: remaining (major) arc ACB=DFE; major=major ⟺ minor=minor for equal circles; no reflex-angle vocab; rendered as ∠a:k:b=∠d:l:e
  euclid_sentence "3.28.9"
    "Thus, the remaining circumference $ACB$ is also equal to the remaining circumference $DFE$."
    (step9 : ∠ a:k:b = ∠ d:l:e) := by sorry

  exact step9
  euclid_conclude_sentence "3.28.10"
    "Thus, in equal circles, equal straight-lines cut off equal circumferences, the greater (circumference being equal) to the greater, and the lesser to the lesser. (Which is) the very thing it was required to show."

end Elements.Book3
