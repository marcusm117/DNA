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

  -- Superposition = "apply △ABC onto △DEF": a fresh congruent copy; images e (of b), c' (of c), g (of a, Euclid's G).
  euclid_apply (superposition b c a e f d BC AC AB EF) as (c', g, GF, EG)
  -- img: the superposition map — b↦e, c↦c', a↦g.
  classical
  let img : Point → Point := fun p =>
    if p = b then e else
    if p = c then c' else
    if p = a then g else
    p

  -- @assumption ("$BC$ being equal to $EF$", |(b─c)| = |(e─f)|)
  euclid_sentence "1.8.1"
    "For if triangle $ABC$ is applied to triangle $DEF$, the point $B$ being placed on point $E$, and the straight-line $BC$ on $EF$, then point $C$ will also coincide with $F$, on account of $BC$ being equal to $EF$."
    (step1 : img c = f) := by sorry

  -- each side coincides via either correspondence; the flipped one is impossible (base fixes b↦e, c↦f).
  -- @assumption ("$BC$ coinciding with $EF$", img b = e ∧ img c = f)
  euclid_sentence "1.8.2"
    "So  (because of) $BC$ coinciding with $EF$,  (the sides) $BA$ and $CA$ will also coincide with  $ED$ and $DF$ (respectively). "
    (step2 : ((img a = d ∧ img b = e) ∨ (img a = e ∧ img b = d)) ∧ ((img a = d ∧ img c = f) ∨ (img a = f ∧ img c = d

    ))) := by sorry

  -- reductio: assume 1.8.3 (both sides fail) → I.7 contradiction; habsurd = ¬(both fail).
  have habsurd : ¬ ((¬ (img a = d ∧ img b = e) ∧ ¬ (img a = e ∧ img b = d)) ∧ (¬ (img a = d ∧ img c = f) ∧ ¬ (img a = f ∧ img c = d))) := by
    intro hne
    -- each side fails: neither correspondence holds (flipped one impossible).
    -- @assumption ("base $BC$ coincides with base $EF$", img b = e ∧ img c = f)
    euclid_sentence "1.8.3"
      "For if base $BC$ coincides with base $EF$, but the sides $AB$ and $AC$  do not coincide with $ED$ and $DF$ (respectively), but miss like $EG$ and $GF$ (in the above figure), "
      (step3 : (¬ (img a = d ∧ img b = e) ∧ ¬ (img a = e ∧ img b = d)) ∧ (¬ (img a = d ∧ img c = f) ∧ ¬ (img a = f ∧ img c = d))) := by sorry
    -- two other lines EG, GF on base EF, equal to the given ED, DF (e f EF redundant/given).
    euclid_sentence "1.8.4"
      "then we will have constructed upon the same straight-line, two other straight-lines equal, respectively, to two (given) straight-lines, "
      (step4 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧ distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|) := by sorry
    euclid_sentence "1.8.5"
      "and (meeting) at a different point on the same side (of the straight-line),"
      (step5 : g ≠ d ∧ g.sameSide d EF) := by sorry
    -- same ends: EG & ED share end E (e on both), GF & DF share end F (f on both).
    euclid_sentence "1.8.6"
      "but having the same ends."
      (step6 : (e.onLine EG ∧ e.onLine DE) ∧ (f.onLine GF ∧ f.onLine DF)) := by sorry
    euclid_sentence "1.8.7"
      "But (such straight-lines) cannot be constructed [Prop.~1.7]."
      (step7 : False) := by sorry
    exact step7

  -- ¬(each side fails), per side (= 1.8.2 in double-negation form).
  euclid_sentence "1.8.8"
    "Thus,  the base $BC$ being applied to the  base $EF$,  the sides $BA$ and $AC$ cannot not coincide with $ED$ and $DF$ (respectively)."
    (step8 : ¬ (¬ (img a = d ∧ img b = e) ∧ ¬ (img a = e ∧ img b = d)) ∧ ¬ (¬ (img a = d ∧ img c = f) ∧ ¬ (img a = f ∧ img c = d))) := by sorry

  euclid_sentence "1.8.9"
    "Thus, they will coincide."
    (step9 : ((img a = d ∧ img b = e) ∨ (img a = e ∧ img b = d)) ∧ ((img a = d ∧ img c = f) ∨ (img a = f ∧ img c = d))) := by sorry

  euclid_sentence "1.8.10"
    "So the angle $BAC$ will also coincide with angle $EDF$, and will be equal to it [C.N.~4]. "
    (step10 : ∠ b:a:c = ∠ e:d:f) := by sorry

  exact step10
  euclid_conclude_sentence "1.8.11"
    "Thus, if two triangles have  two  sides equal to two side, respectively, and  have the base equal to the base, then they will also have equal the angles  encompassed by the equal straight-lines. (Which is) the very thing it was required to show."

end Elements.Book1
