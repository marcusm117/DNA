import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_4 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) →
  |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e) := by
  euclid_intros
  euclid_intro_sentence "1.4.0"
    "If two triangles have two  sides equal to two sides, respectively, and have the angle(s) enclosed by the equal straight-lines equal, then they will also have the base equal to the base, and the triangle will be equal to the triangle,  and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles. Let $ABC$ and $DEF$ be  two triangles having the two sides $AB$ and $AC$ equal to the two sides $DE$ and $DF$, respectively. (That is) $AB$ to $DE$, and $AC$ to $DF$. And (let) the angle $BAC$ (be) equal to the angle $EDF$. I say that the base $BC$ is also equal to the base $EF$, and  triangle $ABC$ will be equal to triangle $DEF$, and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles. (That is) $ABC$ to $DEF$, and $ACB$ to $DFE$."

  -- Superposition = "apply △ABC onto △DEF": apex A placed on D, AB laid on DE.
  -- Outputs: b' = image of B, c' = image of C, BC' = image line of BC, DC' = image line of AC.
  euclid_apply (superposition a b c d e f AB BC AC DE) as (b', c', BC', DC')
  -- ptImg: the superposition map — a↦d (apex placed on D), b↦b', c↦c'.
  classical
  let ptImg : Point → Point := fun p =>
    if p = a then d else
    if p = b then b' else
    if p = c then c' else
    p

  let lineImg : Line → Line := fun L =>
    if L = AB then DE else
    if L = AC then DC' else
    if L = BC then BC' else
    L

  -- @assumption ("$AB$ being equal to $DE$", |(a─b)| = |(d─e)|)
  euclid_sentence "1.4.1"
    "For if triangle $ABC$ is applied to triangle $DEF$, the point $A$ being placed on the point $D$, and the straight-line $AB$ on $DE$, then the point $B$ will also coincide with $E$, on account of $AB$ being equal to $DE$."
    (step1 : ptImg b = e) := by sorry

  -- @assumption ("$AB$ coinciding with $DE$", lineImg AB = DE)
  -- @assumption ("the angle $BAC$ being equal to $EDF$", ∠ b:a:c = ∠ e:d:f)
  euclid_sentence "1.4.2"
    "So (because of) $AB$ coinciding with $DE$, the straight-line $AC$ will also coincide with $DF$, on account of the angle $BAC$ being equal to $EDF$."
    (step2 : lineImg AC = DF) := by sorry

  -- @assumption ("$AC$ being equal to $DF$", |(a─c)| = |(d─f)|)
  euclid_sentence "1.4.3"
    "So the point $C$ will also coincide with the point $F$,  again on account of $AC$ being equal to $DF$. "
    (step3 : ptImg c = f) := by sorry

  -- @assumption ("point $B$  certainly also coincided with point $E$", ptImg b = e)
  euclid_sentence "1.4.4"
    "But,  point $B$  certainly also coincided with point $E$, so that the base $BC$ will coincide with the base $EF$."
    (step4 : lineImg BC = EF) := by sorry

  have habsurd : ¬ (lineImg BC ≠ EF) := by
    intro hne
    -- the assertion here cannot be literally expressed in system E so we do the best we can.
    -- @assumption ("$B$ coincides with $E$", ptImg b = e)
    -- @assumption ("$C$ with $F$", ptImg c = f)
    -- @assumption ("the base $BC$ does not coincide with $EF$", lineImg BC ≠ EF)
    euclid_sentence "1.4.5"
      "For if $B$ coincides with $E$, and $C$ with $F$, and the base $BC$ does not coincide with $EF$, then two straight-lines will encompass an area."
      (step5 : distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF) := by sorry

    euclid_sentence "1.4.6"
      "The very thing is impossible [Post.~1]."
      (step6 : False) := by sorry
    exact step6

  -- @assumption ("the base $BC$ will coincide with $EF$", lineImg BC = EF)
  euclid_sentence "1.4.7"
    "Thus, the base $BC$ will coincide with $EF$, and will be equal to it [C.N.~4]."
    (step7 : |(b─c)| = |(e─f)|) := by sorry

  -- @assumption ("the whole triangle $ABC$ will coincide with the whole triangle $DEF$", ptImg a = d ∧ ptImg b = e ∧ ptImg c = f)
  euclid_sentence "1.4.8"
    "So  the whole triangle $ABC$ will coincide with the whole triangle $DEF$, and will be equal to it [C.N.~4]."
    (step8 : Triangle.area △ a:b:c = Triangle.area △ d:e:f) := by sorry

  -- @assumption ("the remaining angles will coincide with the remaining angles", ptImg a = d ∧ ptImg b = e ∧ ptImg c = f)
  euclid_sentence "1.4.9"
    "And the remaining angles will coincide with the remaining angles, and  will be equal to them [C.N.~4]."
    (step9 : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e) := by sorry

  euclid_sentence "1.4.10"
    "(That is) $ABC$ to $DEF$,"
    (step10 : ∠ a:b:c = ∠ d:e:f) := by sorry

  euclid_sentence "1.4.11"
    "and $ACB$ to $DFE$ [C.N.~4]."
    (step11 : ∠ a:c:b = ∠ d:f:e) := by sorry

  exact ⟨step7, step10, step11⟩
  euclid_conclude_sentence "1.4.12"
    "Thus, if two triangles have two  sides equal to two sides, respectively, and have the angle(s) enclosed by the equal straight-line equal, then they will also have the base equal to the base, and the triangle will be equal to the triangle,  and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles. (Which is) the very thing it was required to show."

end Elements.Book1
