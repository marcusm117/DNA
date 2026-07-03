import SystemE
import Book1.Prop04.step1
import Book1.Prop04.step2
import Book1.Prop04.step3
import Book1.Prop04.step4
import Book1.Prop04.step5
import Book1.Prop04.step6
import Book1.Prop04.step7
import Book1.Prop04.step8
import Book1.Prop04.step9
import Book1.Prop04.step10
import Book1.Prop04.step11
import Book1.Prop04.step8_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

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

  have h_ptImg_a : ptImg a = d := by simp (config := { zetaDelta := true })
  have h_ptImg_b : ptImg b = b' := by simp (config := { zetaDelta := true }) [Ne.symm right_3]
  have h_ptImg_c : ptImg c = c' := by
    have hca : c ≠ a := fun h => left_7 (two_points_determine_line b c AB BC
      ⟨⟨left_3, by rw [h]; assumption, fun heq => right_3 (heq.trans h).symm⟩, left_2, left_4⟩)
    have hcb : c ≠ b := fun h => right_8 (two_points_determine_line a c AB AC
      ⟨⟨by assumption, by rw [h]; assumption, fun heq => right_3 (heq.trans h)⟩, left_6, left_5⟩).symm
    simp (config := { zetaDelta := true }) [hca, hcb]
  have h_lineImg_AB : lineImg AB = DE := by simp (config := { zetaDelta := true })
  have h_lineImg_AC : lineImg AC = DC' := by simp (config := { zetaDelta := true }) [right_8]
  have h_lineImg_BC : lineImg BC = BC' := by
    simp (config := { zetaDelta := true }) [Ne.symm left_7, left_8]

  -- @assumption_valid
  have step1_assumption1 : |(a─b)| = |(d─e)| := by assumption
  -- @assumption ("$AB$ being equal to $DE$", |(a─b)| = |(d─e)|)
  euclid_sentence "1.4.1"
    "For if triangle $ABC$ is applied to triangle $DEF$, the point $A$ being placed on the point $D$, and the straight-line $AB$ on $DE$, then the point $B$ will also coincide with $E$, on account of $AB$ being equal to $DE$."
    (step1 : ptImg b = e) := by euclid_apply (helper_1_4_step1 a b c d e b' c' DE (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─b')|; assumption)) (by euclid_assumption "" (show b'.onLine DE; assumption)) (by euclid_assumption "" (show ¬between b' d e; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "$AB$ being equal to $DE$" (show |(a─b)| = |(d─e)|; assumption)))

  -- @assumption_valid
  have step2_assumption1 : lineImg AB = DE := by simp (config := { zetaDelta := true })
  -- @assumption_valid
  have step2_assumption2 : ∠ b:a:c = ∠ e:d:f := by assumption
  -- @assumption ("$AB$ coinciding with $DE$", lineImg AB = DE)
  -- @assumption ("the angle $BAC$ being equal to $EDF$", ∠ b:a:c = ∠ e:d:f)
  euclid_sentence "1.4.2"
    "So (because of) $AB$ coinciding with $DE$, the straight-line $AC$ will also coincide with $DF$, on account of the angle $BAC$ being equal to $EDF$."
    (step2 : lineImg AC = DF) := by euclid_apply (helper_1_4_step2 a b c d e f b' c' AB BC AC DE EF DF DC' BC' (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "$AB$ coinciding with $DE$" (show lineImg AB = DE; assumption)) (by euclid_assumption "the angle $BAC$ being equal to $EDF$" (show ∠ b:a:c = ∠ e:d:f; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by euclid_assumption "" (show c'.sameSide f DE; assumption)) (by euclid_assumption "" (show d.onLine DC'; assumption)) (by euclid_assumption "" (show c'.onLine DC'; assumption)) (by euclid_assumption "" (show d ≠ c'; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show b'.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show lineImg AC = DC'; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)))

  -- @assumption_valid
  have step3_assumption1 : |(a─c)| = |(d─f)| := by assumption
  -- @assumption ("$AC$ being equal to $DF$", |(a─c)| = |(d─f)|)
  euclid_sentence "1.4.3"
    "So the point $C$ will also coincide with the point $F$,  again on account of $AC$ being equal to $DF$. "
    (step3 : ptImg c = f) := by euclid_apply (helper_1_4_step3 a b c d e f b' c' AC DC' DE DF (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "$AC$ being equal to $DF$" (show |(a─c)| = |(d─f)|; assumption)) (by euclid_assumption "" (show |(c─a)| = |(c'─d)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ e:d:f; assumption)) (by euclid_assumption "" (show c'.sameSide f DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show b'.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show d.onLine DC'; assumption)) (by euclid_assumption "" (show c'.onLine DC'; assumption)) (by euclid_assumption "" (show d ≠ c'; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show lineImg AC = DC'; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)) (by euclid_assumption "" (show lineImg AC = DF; assumption)))

  -- @assumption_valid
  have step4_assumption1 : ptImg b = e := by assumption
  -- @assumption ("point $B$  certainly also coincided with point $E$", ptImg b = e)
  euclid_sentence "1.4.4"
    "But,  point $B$  certainly also coincided with point $E$, so that the base $BC$ will coincide with the base $EF$."
    (step4 : lineImg BC = EF) := by euclid_apply (helper_1_4_step4 b c e f b' c' BC BC' EF (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "point $B$  certainly also coincided with point $E$" (show ptImg b = e; assumption)) (by euclid_assumption "" (show b'.onLine BC'; assumption)) (by euclid_assumption "" (show c'.onLine BC'; assumption)) (by euclid_assumption "" (show b' ≠ c'; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show lineImg BC = BC'; assumption)) (by euclid_assumption "point $B$  certainly also coincided with point $E$" (show ptImg b = e; assumption)) (by euclid_assumption "" (show ptImg c = f; assumption)))

  have habsurd : ¬ (lineImg BC ≠ EF) := by
    intro hne
    -- the assertion here cannot be literally expressed in system E so we do the best we can.
    -- @assumption_valid
    have step5_assumption1 : ptImg b = e := by assumption
    -- @assumption_valid
    have step5_assumption2 : ptImg c = f := by assumption
    -- @assumption_valid
    have step5_assumption3 : lineImg BC ≠ EF := by assumption
    -- @assumption ("$B$ coincides with $E$", ptImg b = e)
    -- @assumption ("$C$ with $F$", ptImg c = f)
    -- @assumption ("the base $BC$ does not coincide with $EF$", lineImg BC ≠ EF)
    euclid_sentence "1.4.5"
      "For if $B$ coincides with $E$, and $C$ with $F$, and the base $BC$ does not coincide with $EF$, then two straight-lines will encompass an area."
      (step5 : distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF) := by euclid_apply (helper_1_4_step5 b c e f b' c' BC BC' EF (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "$B$ coincides with $E$" (show ptImg b = e; assumption)) (by euclid_assumption "$C$ with $F$" (show ptImg c = f; assumption)) (by euclid_assumption "the base $BC$ does not coincide with $EF$" (show lineImg BC ≠ EF; assumption)) (by euclid_assumption "" (show b'.onLine BC'; assumption)) (by euclid_assumption "" (show c'.onLine BC'; assumption)) (by euclid_assumption "" (show b' ≠ c'; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show lineImg BC = BC'; assumption)) (by euclid_assumption "$B$ coincides with $E$" (show ptImg b = e; assumption)) (by euclid_assumption "$C$ with $F$" (show ptImg c = f; assumption)))

    euclid_sentence "1.4.6"
      "The very thing is impossible [Post.~1]."
      (step6 : False) := by euclid_apply (helper_1_4_step6 e f BC BC' EF (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "" (show lineImg BC ≠ EF; assumption)) (by euclid_assumption "" (show lineImg BC = BC'; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF; assumption)))
    exact step6

  -- @assumption_valid
  have step7_assumption1 : lineImg BC = EF := by assumption
  -- @assumption ("the base $BC$ will coincide with $EF$", lineImg BC = EF)
  euclid_sentence "1.4.7"
    "Thus, the base $BC$ will coincide with $EF$, and will be equal to it [C.N.~4]."
    (step7 : |(b─c)| = |(e─f)|) := by euclid_apply (helper_1_4_step7 b c e f b' c' BC EF (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show Line → Line; assumption)) (by euclid_assumption "the base $BC$ will coincide with $EF$" (show lineImg BC = EF; assumption)) (by euclid_assumption "" (show |(b─c)| = |(b'─c')|; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)) (by euclid_assumption "" (show ptImg c = f; assumption)))

  -- @assumption_gap
  have step8_assumption1 : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f := by euclid_apply (helper_1_4_step8_assumption1 a b c d e f b' c' (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ptImg a = d; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)) (by euclid_assumption "" (show ptImg c = f; assumption)))
  -- @assumption ("the whole triangle $ABC$ will coincide with the whole triangle $DEF$", ptImg a = d ∧ ptImg b = e ∧ ptImg c = f)
  euclid_sentence "1.4.8"
    "So  the whole triangle $ABC$ will coincide with the whole triangle $DEF$, and will be equal to it [C.N.~4]."
    (step8 : Triangle.area △ a:b:c = Triangle.area △ d:e:f) := by euclid_apply (helper_1_4_step8 a b c d e f b' c' (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "the whole triangle $ABC$ will coincide with the whole triangle $DEF$" (show ptImg a = d ∧ ptImg b = e ∧ ptImg c = f; assumption)) (by euclid_assumption "" (show |(a─b)| = |(d─e)|; assumption)) (by euclid_assumption "" (show |(a─c)| = |(d─f)|; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ d:c':b'; assumption)) (by euclid_assumption "" (show ∠ c:b:a = ∠ c':b':d; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)) (by euclid_assumption "" (show ptImg c = f; assumption)) (by euclid_assumption "" (show |(b─c)| = |(e─f)|; assumption)))


  euclid_sentence "1.4.9"
    "And the remaining angles will coincide with the remaining angles, and  will be equal to them [C.N.~4]."
    (step9 : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e) := by euclid_apply (helper_1_4_step9 b c e f b' c' (by euclid_assumption "" (show Point → Point; assumption)) (by euclid_assumption "" (show ptImg a = d ∧ ptImg b = e ∧ ptImg c = f; assumption)) (by euclid_assumption "" (show ∠ a:c:b = ∠ d:c':b'; assumption)) (by euclid_assumption "" (show ∠ c:b:a = ∠ c':b':d; assumption)) (by euclid_assumption "" (show ptImg b = b'; assumption)) (by euclid_assumption "" (show ptImg c = c'; assumption)) (by euclid_assumption "" (show ptImg b = e; assumption)) (by euclid_assumption "" (show ptImg c = f; assumption)) (by euclid_assumption "" (show |(b─c)| = |(b'─c')|; assumption)) (by euclid_assumption "" (show b' ≠ c'; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)))

  euclid_sentence "1.4.10"
    "(That is) $ABC$ to $DEF$,"
    (step10 : ∠ a:b:c = ∠ d:e:f) := by euclid_apply (helper_1_4_step10 (by euclid_assumption "" (show ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e; assumption)))

  euclid_sentence "1.4.11"
    "and $ACB$ to $DFE$ [C.N.~4]."
    (step11 : ∠ a:c:b = ∠ d:f:e) := by euclid_apply (helper_1_4_step11 (by euclid_assumption "" (show ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e; assumption)))

  exact ⟨step7, step10, step11⟩
  euclid_conclude_sentence "1.4.12"
    "Thus, if two triangles have two  sides equal to two sides, respectively, and have the angle(s) enclosed by the equal straight-line equal, then they will also have the base equal to the base, and the triangle will be equal to the triangle,  and the remaining angles subtended by the equal sides will be equal to the corresponding remaining angles. (Which is) the very thing it was required to show."

end Elements.Book1
