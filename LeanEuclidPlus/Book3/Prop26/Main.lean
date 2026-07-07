import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_26 : ∀ (a b c d e f g h : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  g.isCentre ABC ∧ h.isCentre DEF ∧
  |(g─b)| = |(h─e)| ∧
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
  ∠ b:a:c = ∠ e:d:f →
  ∠ b:g:c = ∠ e:h:f :=
by
  euclid_intros
  euclid_intro_sentence "3.26.0"
    "In equal circles, equal angles stand upon equal circumferences whether they are standing at the center or at the circumference. Let $ABC$ and $DEF$ be equal circles, and within them let $BGC$ and $EHF$ be equal angles at the center, and $BAC$ and $EDF$ (equal angles) at the circumference. I say that circumference $BKC$ is equal to circumference $ELF$."

  euclid_apply (line_from_points b c) as BC
  euclid_apply (line_from_points e f) as EF
  euclid_sentence "3.26.1"
    "For let $BC$ and $EF$ be joined."
    (step1 : distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF) := by sorry

  -- @assumption ("circles $ABC$ and $DEF$ are equal", |(g─b)| = |(h─e)|)
  euclid_sentence "3.26.2"
    "And since circles $ABC$ and $DEF$ are equal, their radii are equal."
    (step2 : |(g─b)| = |(h─e)| ∧ |(g─c)| = |(h─f)|) := by sorry

  euclid_sentence "3.26.3"
    "So the two (straight-lines) $BG$, $GC$ (are) equal to the two (straight-lines) $EH$, $HF$ (respectively)."
    (step3 : |(g─b)| = |(h─e)| ∧ |(g─c)| = |(h─f)|) := by sorry

  -- orchestrator-centralAngle: step4 = central angle equality ∠b:g:c=∠e:h:f; in the locked signature
  -- (inscribed-angle hyp only), this must be proved in Phase B via [III.20] (inscribed=half central);
  -- in Euclid's full proof it was a given (BGC=EHF central angle hyp), but our sig takes only ∠b:a:c=∠e:d:f.
  euclid_sentence "3.26.4"
    "And the angle at $G$ (is) equal to the angle at $H$."
    (step4 : ∠ b:g:c = ∠ e:h:f) := by sorry

  euclid_sentence "3.26.5"
    "Thus, the base $BC$ is equal to the base $EF$ [Prop.~1.4]."
    (step5 : |(b─c)| = |(e─f)|) := by sorry

  -- @assumption ("the angle at $A$ is equal to the (angle) at $D$", ∠ b:a:c = ∠ e:d:f)
  -- orchestrator-segmentSimilarity: "segment BAC similar to EDF" per Def.3.11 = equal inscribed angles;
  -- System E has no separate segment-similarity predicate; the only expressible content of
  -- Def.3.11 IS the inscribed angle equality (the given hyp); claim = ∠b:a:c=∠e:d:f; RULE-2
  -- tension acknowledged — no richer System-E expression exists with ZERO new vocab.
  euclid_sentence "3.26.6"
    "And since the angle at $A$ is equal to the (angle) at $D$, the segment $BAC$ is thus similar to the segment $EDF$ [Def.~3.11]."
    (step6 : ∠ b:a:c = ∠ e:d:f) := by sorry

  euclid_sentence "3.26.7"
    "And they are on equal straight-lines [$BC$ and $EF$]."
    (step7 : |(b─c)| = |(e─f)|) := by sorry

  -- orchestrator-arcCentralAngle: Prop3.24 applied to segments BAC/EDF: "similar segments on equal
  -- straight-lines are equal"; in arc-as-central-angle convention, segment equality = major arc
  -- equality ↔ minor arc equality ↔ ∠b:g:c=∠e:h:f (primer §arc-as-magnitude, "major=major ↔
  -- minor complements equal"); Prop3.24 can't be directly called (different-center circles, different
  -- chord lines); claim = the arc-equality consequent in System E.
  euclid_sentence "3.26.8"
    "And similar segments of circles on equal straight-lines are equal to one another [Prop.~3.24]."
    (step8 : ∠ b:g:c = ∠ e:h:f) := by sorry

  -- orchestrator-arcCentralAngle: "segment BAC = segment EDF" → equal major arcs BAC/EDF
  -- ↔ equal minor arcs BKC/ELF ↔ ∠b:g:c=∠e:h:f.
  euclid_sentence "3.26.9"
    "Thus, segment $BAC$ is equal to (segment) $EDF$."
    (step9 : ∠ b:g:c = ∠ e:h:f) := by sorry

  -- orchestrator-equalCircles: "whole circle ABC = whole circle DEF" = equal circles (Euclid's
  -- sense = equal radii); System E encodes this as |(g─b)|=|(h─e)| (the given hyp); claim restates
  -- the given — unavoidable with ZERO new vocab and different-center circles in our signature.
  euclid_sentence "3.26.10"
    "And the whole circle $ABC$ is also equal to the whole circle $DEF$."
    (step10 : |(g─b)| = |(h─e)|) := by sorry

  -- orchestrator-arcCentralAngle: "remaining circumference BKC = ELF" = minor arc BKC = minor arc ELF
  -- = ∠b:g:c=∠e:h:f (goal); derived by C.N.3: equal circles (step10) minus equal segments (step9)
  -- leaves equal remaining arcs; in arc-as-central-angle: 4∟ - major_arc_BAC = 4∟ - major_arc_EDF
  -- ↔ ∠b:g:c=∠e:h:f.
  euclid_sentence "3.26.11"
    "Thus, the remaining circumference $BKC$ is equal to the (remaining) circumference $ELF$."
    (step11 : ∠ b:g:c = ∠ e:h:f) := by sorry

  exact step11
  euclid_conclude_sentence "3.26.12"
    "Thus, in equal circles, equal angles stand upon equal circumferences, whether they are standing at the center or at the circumference. (Which is) the very thing which it was required to show."

end Elements.Book3
