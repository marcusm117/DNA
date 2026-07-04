import SystemE
import Book.Prop03
import Book.Prop04
import Book.Prop16
import Mathlib.Tactic.Linarith
import Book1.Prop26.h_sym
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem proposition_26 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) := by
  euclid_intros
  euclid_intro_sentence "1.26.0"
    "If  two triangles have two angles equal to two angles, respectively,  and one side equal to one side---in fact, either that by the equal angles, or that subtending one of the equal angles---then (the triangles) will also have the remaining sides equal to the [corresponding] remaining sides, and the remaining angle (equal) to the remaining angle.  Let $ABC$ and $DEF$ be two triangles having the two angles $ABC$ and $BCA$ equal to the two (angles) $DEF$ and $EFD$, respectively. (That is) $ABC$ (equal) to $DEF$, and $BCA$ to $EFD$. And let them also have one side equal to one side. First of all, the (side) by the equal angles. (That is) $BC$ (equal) to $EF$. I say that they will have the  remaining sides equal to the corresponding remaining sides. (That is) $AB$ (equal) to $DE$, and $AC$ to $DF$. And (they will have) the remaining angle (equal) to the remaining angle. (That is) $BAC$ (equal) to $EDF$."

  split_ors

  -- Case 1: hbc : |(b─c)| = |(e─f)|
  ·
    have habsurd1 : ¬(|(a─b)| ≠ |(d─e)|) := by
      intro hne
      euclid_sentence "1.26.1"
        " For if $AB$ is unequal to $DE$ then one of them is greater."
        (step1 : |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|) := by sorry
      wlog hgt : |(a─b)| > |(d─e)| generalizing a b c d e f AB BC AC DE EF DF with Hsym
      -- Reduction: ¬(AB > DE); by step1 DE > AB; symmetric argument with swapped triangles
      ·
        have h_sym : False := by euclid_apply (helper_1_26_h_sym a b c d e f AB BC AC DE EF DF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show DE ≠ EF; assumption)) (by euclid_assumption "" (show EF ≠ DF; assumption)) (by euclid_assumption "" (show DF ≠ DE; assumption)) (by euclid_assumption "" (show ∠ a:b:c = ∠ d:e:f; assumption)) (by euclid_assumption "" (show ∠ b:c:a = ∠ e:f:d; assumption)) (by euclid_assumption "" (show |(b─c)| = |(e─f)|; assumption)) (by euclid_assumption "" (show |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|; assumption)) (by euclid_assumption "" (show ¬|(a─b)| > |(d─e)|; assumption)))
        exact h_sym
      · euclid_apply (proposition_3 b a e d AB DE) as g
        euclid_apply (line_from_points g c) as GC
        euclid_sentence "1.26.2"
          "Let $AB$ be greater, and let $BG$ be made equal to $DE$ [Prop.~1.3], and let $GC$ have been joined."
          (step2 : between b g a ∧ |(b─g)| = |(d─e)| ∧ g.onLine GC ∧ c.onLine GC) := by sorry
        -- @assumption_valid
        have step3_assumption1 : |(b─g)| = |(d─e)| := by linarith
        -- @assumption_valid
        have step3_assumption2 : |(b─c)| = |(e─f)| := by assumption
        -- @assumption ("$BG$ is equal to $DE$", |(b─g)| = |(d─e)|)
        -- @assumption ("$BC$ to $EF$", |(b─c)| = |(e─f)|)
        euclid_sentence "1.26.3"
          " Therefore, since $BG$ is equal to $DE$, and $BC$ to $EF$, the two (straight-lines) $GB$, $BC$ are equal to the two (straight-lines) $DE$, $EF$, respectively."
          (step3 : |(g─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)|) := by sorry
        euclid_sentence "1.26.4"
          "And angle $GBC$ is equal to angle $DEF$."
          (step4 : ∠ g:b:c = ∠ d:e:f) := by sorry
        euclid_sentence "1.26.5"
          "Thus, the base $GC$ is equal to the base $DF$,"
          (step5 : |(g─c)| = |(d─f)|) := by sorry
        euclid_sentence "1.26.6"
          "and triangle $GBC$ is equal to triangle $DEF$,"
          (step6 : Triangle.area △ g:b:c = Triangle.area △ d:e:f) := by sorry
        euclid_sentence "1.26.7"
          "and the remaining angles  subtended by the equal sides will be equal to the (corresponding) remaining angles [Prop.~1.4]."
          (step7 : ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e) := by sorry
        euclid_sentence "1.26.8"
          "Thus, $GCB$ (is equal) to $DFE$."
          (step8 : ∠ g:c:b = ∠ d:f:e) := by sorry
        euclid_sentence "1.26.9"
          "But,  $DFE$ was assumed (to be) equal to $BCA$."
          (step9 : ∠ d:f:e = ∠ b:c:a) := by sorry
        euclid_sentence "1.26.10"
          "Thus, $BCG$ is also equal to $BCA$, the lesser to the greater."
          (step10 : ∠ b:c:g = ∠ b:c:a) := by sorry
        euclid_sentence "1.26.11"
          "The very thing (is) impossible."
          (step11 : False) := by sorry
        exact step11

    euclid_sentence "1.26.12"
      "Thus, $AB$ is not unequal to $DE$."
      (step12 : ¬(|(a─b)| ≠ |(d─e)|)) := by sorry
    euclid_sentence "1.26.13"
      "Thus, (it is) equal."
      (step13 : |(a─b)| = |(d─e)|) := by sorry
    euclid_sentence "1.26.14"
      "And $BC$ is also equal to $EF$."
      (step14 : |(b─c)| = |(e─f)|) := by sorry
    euclid_sentence "1.26.15"
      "So the two (straight-lines) $AB$, $BC$ are equal to the two (straight-lines) $DE$, $EF$, respectively."
      (step15 : |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)|) := by sorry
    euclid_sentence "1.26.16"
      "And angle $ABC$ is equal to angle $DEF$."
      (step16 : ∠ a:b:c = ∠ d:e:f) := by sorry
    euclid_sentence "1.26.17"
      "Thus, the base $AC$ is equal to the base $DF$,"
      (step17 : |(a─c)| = |(d─f)|) := by sorry
    euclid_sentence "1.26.18"
      "and the remaining angle $BAC$ is equal to the remaining angle $EDF$ [Prop.~1.4]."
      (step18 : ∠ b:a:c = ∠ e:d:f) := by sorry
    exact ⟨step13, step14, step17, step18⟩

  -- Case 2: hab : |(a─b)| = |(d─e)|
  ·
    euclid_sentence "1.26.19"
      " But, again, let the sides subtending the equal angles be equal: for instance,  (let) $AB$ (be equal) to $DE$."
      (step19 : |(a─b)| = |(d─e)|) := by sorry
    euclid_wts "1.26.20"
      " Again, I say that the remaining sides will be equal to the remaining sides."
    euclid_wts "1.26.21"
      "(That is) $AC$ (equal) to $DF$,"
    euclid_wts "1.26.22"
      "and $BC$ to $EF$."
    euclid_wts "1.26.23"
      "Furthermore, the remaining angle $BAC$ is equal to the remaining angle $EDF$."
    have habsurd2 : ¬(|(b─c)| ≠ |(e─f)|) := by
      intro hne2
      euclid_sentence "1.26.24"
        " For if $BC$ is unequal to $EF$ then one of them is greater."
        (step24 : |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)|) := by sorry
      wlog hgt2 : |(b─c)| > |(e─f)| generalizing a b c d e f AB BC AC DE EF DF with Hsym2
      -- Reduction: ¬(BC > EF); by step24 EF > BC; symmetric argument with swapped triangles
      ·
        have h_sym2 : False := by sorry
        exact h_sym2
      · euclid_apply (proposition_3 b c e f BC EF) as h
        euclid_apply (line_from_points a h) as AH
        euclid_sentence "1.26.25"
          "If possible, let $BC$ be greater. And let $BH$ be made equal to $EF$ [Prop.~1.3], and let $AH$ have been joined."
          (step25 : between b h c ∧ |(b─h)| = |(e─f)| ∧ a.onLine AH ∧ h.onLine AH) := by sorry
        -- @assumption_valid
        have step26_assumption1 : |(b─h)| = |(e─f)| := by assumption
        -- @assumption_valid
        have step26_assumption2 : |(a─b)| = |(d─e)| := by assumption
        -- @assumption ("$BH$ is equal to $EF$", |(b─h)| = |(e─f)|)
        -- @assumption ("$AB$ to $DE$", |(a─b)| = |(d─e)|)
        euclid_sentence "1.26.26"
          "And since $BH$ is equal to $EF$, and $AB$ to $DE$, the two (straight-lines) $AB$, $BH$ are equal to the two (straight-lines) $DE$, $EF$, respectively."
          (step26 : |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|) := by sorry
        euclid_sentence "1.26.27"
          "And the angles they encompass (are also equal)."
          (step27 : ∠ a:b:h = ∠ d:e:f) := by sorry
        euclid_sentence "1.26.28"
          "Thus, the base $AH$ is equal to the base   $DF$,"
          (step28 : |(a─h)| = |(d─f)|) := by sorry
        euclid_sentence "1.26.29"
          "and the triangle $ABH$ is equal to the triangle $DEF$,"
          (step29 : Triangle.area △ a:b:h = Triangle.area △ d:e:f) := by sorry
        euclid_sentence "1.26.30"
          "and the remaining angles subtended by the equal sides will be equal to the (corresponding) remaining angles [Prop.~1.4]."
          (step30 : ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d) := by sorry
        euclid_sentence "1.26.31"
          "Thus, angle $BHA$  is equal to $EFD$."
          (step31 : ∠ b:h:a = ∠ e:f:d) := by sorry
        euclid_sentence "1.26.32"
          "But, $EFD$ is equal to $BCA$."
          (step32 : ∠ e:f:d = ∠ b:c:a) := by sorry
        euclid_sentence "1.26.33"
          "So, in triangle $AHC$, the external angle $BHA$ is equal to the internal and opposite angle  $BCA$."
          (step33 : ∠ b:h:a = ∠ b:c:a) := by sorry
        euclid_sentence "1.26.34"
          "The very thing (is) impossible [Prop.~1.16]."
          (step34 : False) := by sorry
        exact step34

    euclid_sentence "1.26.35"
      "Thus, $BC$ is not unequal to $EF$."
      (step35 : ¬(|(b─c)| ≠ |(e─f)|)) := by sorry
    euclid_sentence "1.26.36"
      "Thus, (it is) equal."
      (step36 : |(b─c)| = |(e─f)|) := by sorry
    euclid_sentence "1.26.37"
      "And $AB$ is also equal to $DE$."
      (step37 : |(a─b)| = |(d─e)|) := by sorry
    euclid_sentence "1.26.38"
      "So the two (straight-lines) $AB$, $BC$ are equal to the two (straight-lines) $DE$, $EF$, respectively."
      (step38 : |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)|) := by sorry
    euclid_sentence "1.26.39"
      "And they encompass equal angles."
      (step39 : ∠ a:b:c = ∠ d:e:f) := by sorry
    euclid_sentence "1.26.40"
      "Thus, the base $AC$ is equal to the base $DF$,"
      (step40 : |(a─c)| = |(d─f)|) := by sorry
    euclid_sentence "1.26.41"
      "and triangle $ABC$ (is) equal to triangle $DEF$,"
      (step41 : Triangle.area △ a:b:c = Triangle.area △ d:e:f) := by sorry
    euclid_sentence "1.26.42"
      "and the remaining angle $BAC$ (is) equal to the remaining angle $EDF$ [Prop.~1.4]."
      (step42 : ∠ b:a:c = ∠ e:d:f) := by sorry
    exact ⟨step37, step36, step40, step42⟩

  euclid_conclude_sentence "1.26.43"
    " Thus, if two triangles have two angles equal to two angles, respectively,  and one side equal to one side---in fact, either that by the equal angles, or that subtending one of the equal angles---then (the triangles) will also have the remaining sides equal to the (corresponding) remaining sides, and the remaining angle (equal) to the remaining angle. (Which is) the very thing it was required to show."

end Elements.Book1
