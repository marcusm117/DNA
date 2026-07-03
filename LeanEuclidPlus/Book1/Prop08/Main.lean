import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_8 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| →
  ∠ b:a:c = ∠ e:d:f := by
  euclid_intros
  euclid_intro_sentence "1.8.0"
    "If two triangles have  two sides equal to two sides, respectively,  and also have the base equal to the base, then they will also have equal the angles  encompassed by the equal straight-lines.      Let $ABC$ and $DEF$ be two triangles having the two sides $AB$ and $AC$ equal to the two sides $DE$ and $DF$, respectively. (That is) $AB$ to $DE$, and $AC$ to $DF$.  Let them also have the base $BC$ equal to the base $EF$. I say that the angle $BAC$ is also equal to the angle $EDF$. "

  -- Superposition = "apply △ABC onto △DEF", base BC onto EF: images e (of b), c' (of c), g (of a, Euclid's G).
  euclid_apply (superposition b c a e f d BC AC AB EF) as (c', g, GF, EG)
  -- ptImg: b↦e, c↦c', a↦g.  lineImg: BC↦EF (base placed), AB↦EG, AC↦GF (the images of the sides).
  classical
  let ptImg : Point → Point := fun p =>
    if p = b then e else
    if p = c then c' else
    if p = a then g else
    p
  let lineImg : Line → Line := fun L =>
    if L = BC then EF else
    if L = AB then EG else
    if L = AC then GF else
    L

  -- @assumption_valid
  have step1_assumption1 : |(b─c)| = |(e─f)| := by assumption
  -- @assumption ("$BC$ being equal to $EF$", |(b─c)| = |(e─f)|)
  euclid_sentence "1.8.1"
    "For if triangle $ABC$ is applied to triangle $DEF$, the point $B$ being placed on point $E$, and the straight-line $BC$ on $EF$, then point $C$ will also coincide with $F$, on account of $BC$ being equal to $EF$."
    (step1 : ptImg c = f) := by sorry

  -- @assumption_valid
  have step2_assumption1 : lineImg BC = EF := by simp (config := { zetaDelta := true })
  -- @assumption ("$BC$ coinciding with $EF$", lineImg BC = EF)
  euclid_sentence "1.8.2"
    "So  (because of) $BC$ coinciding with $EF$,  (the sides) $BA$ and $CA$ will also coincide with  $ED$ and $DF$ (respectively). "
    (step2 : lineImg AB = DE ∧ lineImg AC = DF) := by sorry

  have habsurd : ¬ (lineImg AB ≠ DE ∧ lineImg AC ≠ DF) := by
    intro hne
    -- @assumption_valid
    have step3_assumption1 : lineImg BC = EF := by assumption
    -- @assumption ("base $BC$ coincides with base $EF$", lineImg BC = EF)
    euclid_sentence "1.8.3"
      "For if base $BC$ coincides with base $EF$, but the sides $AB$ and $AC$  do not coincide with $ED$ and $DF$ (respectively), but miss like $EG$ and $GF$ (in the above figure), "
      (step3 : lineImg AB ≠ DE ∧ lineImg AC ≠ DF) := by sorry
    euclid_sentence "1.8.4"
      "then we will have constructed upon the same straight-line, two other straight-lines equal, respectively, to two (given) straight-lines, "
      (step4 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧ distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|) := by sorry
    euclid_sentence "1.8.5"
      "and (meeting) at a different point on the same side (of the straight-line),"
      (step5 : g ≠ d ∧ g.sameSide d EF) := by sorry
    euclid_sentence "1.8.6"
      "but having the same ends."
      (step6 : (e.onLine EG ∧ e.onLine DE) ∧ (f.onLine GF ∧ f.onLine DF)) := by sorry
    euclid_sentence "1.8.7"
      "But (such straight-lines) cannot be constructed [Prop.~1.7]."
      (step7 : False) := by sorry
    exact step7

  euclid_sentence "1.8.8"
    "Thus,  the base $BC$ being applied to the  base $EF$,  the sides $BA$ and $AC$ cannot not coincide with $ED$ and $DF$ (respectively)."
    (step8 : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF)) := by sorry

  euclid_sentence "1.8.9"
    "Thus, they will coincide."
    (step9 : lineImg AB = DE ∧ lineImg AC = DF) := by sorry

  euclid_sentence "1.8.10"
    "So the angle $BAC$ will also coincide with angle $EDF$, and will be equal to it [C.N.~4]. "
    (step10 : ∠ b:a:c = ∠ e:d:f) := by sorry

  exact step10
  euclid_conclude_sentence "1.8.11"
    "Thus, if two triangles have  two  sides equal to two side, respectively, and  have the base equal to the base, then they will also have equal the angles  encompassed by the equal straight-lines. (Which is) the very thing it was required to show."

end Elements.Book1
