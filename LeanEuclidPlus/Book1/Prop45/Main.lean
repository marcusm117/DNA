import SystemE
import Book.Prop42
import Book.Prop44
import Book1.Prop45.step1
import Book1.Prop45.step2
import Book1.Prop45.step3
import Book1.Prop45.step4
import Book1.Prop45.step5
import Book1.Prop45.step6
import Book1.Prop45.step7
import Book1.Prop45.step8
import Book1.Prop45.step9
import Book1.Prop45.step10
import Book1.Prop45.step11
import Book1.Prop45.step12
import Book1.Prop45.step13
import Book1.Prop45.step14
import Book1.Prop45.step15
import Book1.Prop45.step16
import Book1.Prop45.step17
import Book1.Prop45.step18
import Book1.Prop45.step19
import Book1.Prop45.step20
import Book1.Prop45.step21
import Book1.Prop45.step17_assumption1
import Book1.Prop45.step17_assumption2
import Book1.Prop45.hangle
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_45 : ∀ (a b c d e₁ e₂ e₃ : Point) (AB BC CD AD DB E₁₂ E₂₃ : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB ∧
  formRectilinearAngle e₁ e₂ e₃ E₁₂ E₂₃ ∧ ∠ e₁:e₂:e₃ > 0 ∧ ∠ e₁:e₂:e₃ < ∟ + ∟ →
  ∃ (f l k m : Point) (FL KM FK LM : Line), formParallelogram f l k m FL KM FK LM ∧
  (∠ f:k:m = ∠ e₁:e₂:e₃) ∧ (Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by
  euclid_intros
  euclid_intro_sentence "1.45.0"
    "To construct a parallelogram equal to a given rectilinear figure in a given rectilinear angle.  Let $ABCD$ be the given rectilinear figure, and $E$ the given rectilinear angle. So it is required to construct a parallelogram equal to the rectilinear figure $ABCD$ in the given angle $E$. "

  euclid_sentence "1.45.1"
    "Let $DB$ have been joined,"
    (step1 : distinctPointsOnLine d b DB) := by euclid_apply (helper_1_45_step1 a b d AB DB AD (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))

  euclid_apply (proposition_42 a b d e₁ e₂ e₃ AB DB AD E₁₂ E₂₃) as (f, g, k, h, FG, KH, FK, GH)
  euclid_sentence "1.45.2"
    "and let the parallelogram $FH$, equal to the triangle $ABD$, have been constructed in the angle $HKF$, which is equal to $E$ [Prop.~1.42]."
    (step2 : formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)) := by euclid_apply (helper_1_45_step2 f g k h FG KH FK GH e₁ e₂ e₃ a b d (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)) (by euclid_assumption "" (show ∠h:k:f = ∠e₁:e₂:e₃; assumption)) (by euclid_assumption "" (show Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d; assumption)))

  euclid_apply (proposition_44' g h d b c e₁ e₂ e₃ k GH DB BC CD E₁₂ E₂₃) as (m, l, HM, GL, LM)
  euclid_sentence "1.45.3"
    "And let the parallelogram $GM$, equal to the triangle $DBC$, have been applied to the straight-line $GH$ in the angle $GHM$, which is equal to $E$ [Prop.~1.44]."
    (step3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)) := by euclid_apply (helper_1_45_step3 h m g l HM GL GH LM e₁ e₂ e₃ d b c (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)) (by euclid_assumption "" (show ¬HM.intersectsLine GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)) (by euclid_assumption "" (show ∠g:h:m = ∠e₁:e₂:e₃; assumption)) (by euclid_assumption "" (show Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c; assumption)))

  -- @assumption_valid
  have step4_assumption1 : ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m := by euclid_finish
  -- @assumption ("angle $E$ is equal to each of (angles) $HKF$ and $GHM$", ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m)
  euclid_sentence "1.45.4"
    "And since angle $E$ is equal to each of (angles) $HKF$ and $GHM$,  (angle) $HKF$ is thus also equal to $GHM$. "
    (step4 : ∠ h:k:f = ∠ g:h:m) := by euclid_apply (helper_1_45_step4 e₁ e₂ e₃ h k f g m (by euclid_assumption "angle $E$ is equal to each of (angles) $HKF$ and $GHM$" (show ∠ e₁:e₂:e₃ = ∠ h:k:f ∧ ∠ e₁:e₂:e₃ = ∠ g:h:m; assumption)))

  euclid_sentence "1.45.5"
    "Let $KHG$ have been added to both."
    (step5 : ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g) := by euclid_apply (helper_1_45_step5 h k f g m (by euclid_assumption "" (show ∠ h:k:f = ∠ g:h:m; assumption)))

  euclid_sentence "1.45.6"
    "Thus, (the sum of) $FKH$ and $KHG$ is equal to (the sum of) $KHG$ and $GHM$."
    (step6 : ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m) := by euclid_apply (helper_1_45_step6 f k h g m FG KH GH (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ∠ h:k:f + ∠ k:h:g = ∠ g:h:m + ∠ k:h:g; assumption)))

  euclid_sentence "1.45.7"
    "But, (the sum of) $FKH$ and $KHG$ is equal to two right-angles [Prop.~1.29]."
    (step7 : ∠ f:k:h + ∠ k:h:g = ∟ + ∟) := by euclid_apply (helper_1_45_step7 f g k h FK GH KH FG (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)))

  euclid_sentence "1.45.8"
    "Thus, (the sum of) $KHG$ and $GHM$ is also equal to two right-angles."
    (step8 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by euclid_apply (helper_1_45_step8 f g k h m (by euclid_assumption "" (show ∠ f:k:h + ∠ k:h:g = ∠ k:h:g + ∠ g:h:m; assumption)) (by euclid_assumption "" (show ∠ f:k:h + ∠ k:h:g = ∟ + ∟; assumption)))

  euclid_sentence "1.45.9"
    "So two straight-lines, $KH$ and $HM$, not lying on the same side, make  adjacent angles with some straight-line $GH$,  at the point $H$ on it, (whose sum is) equal to two right-angles."
    (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟)) := by euclid_apply (helper_1_45_step9 k m g h GH (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)) (by euclid_assumption "" (show ∠ k:h:g + ∠ g:h:m = ∟ + ∟; assumption)))

  euclid_sentence "1.45.10"
    "Thus, $KH$ is straight-on to $HM$ [Prop.~1.14]."
    (step10 : KH = HM) := by euclid_apply (helper_1_45_step10 g k h m GH KH HM (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)))

  -- @assumption_valid
  have step11_assumption1 : ¬(FG.intersectsLine KH) := by assumption
  -- @assumption ("the straight-line $HG$ falls across the parallels $KM$ and $FG$", ¬(FG.intersectsLine KH))
  euclid_sentence "1.45.11"
    "And since the straight-line $HG$ falls across the parallels $KM$ and $FG$, the alternate angles $MHG$ and $HGF$ are equal to one another [Prop.~1.29]."
    (step11 : ∠ m:h:g = ∠ h:g:f) := by euclid_apply (helper_1_45_step11 f g k h m FG GH KH HM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "the straight-line $HG$ falls across the parallels $KM$ and $FG$" (show ¬(FG.intersectsLine KH); assumption)))

  euclid_sentence "1.45.12"
    "Let $HGL$ have been added to both."
    (step12 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l) := by euclid_apply (helper_1_45_step12 f g h m l (by euclid_assumption "" (show ∠ m:h:g = ∠ h:g:f; assumption)))

  euclid_sentence "1.45.13"
    "Thus, (the sum of) $MHG$ and $HGL$ is equal to  (the sum of) $HGF$ and $HGL$."
    (step13 : ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l) := by euclid_apply (helper_1_45_step13 f g h m l (by euclid_assumption "" (show ∠ m:h:g = ∠ h:g:f; assumption)))

  euclid_sentence "1.45.14"
    "But, (the sum of) $MHG$ and $HGL$ is equal to two right-angles [Prop.~1.29]."
    (step14 : ∠ m:h:g + ∠ h:g:l = ∟ + ∟) := by euclid_apply (helper_1_45_step14 g h m l GL HM GH LM (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show ¬HM.intersectsLine GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))

  euclid_sentence "1.45.15"
    "Thus, (the sum of) $HGF$ and $HGL$ is also equal to two right-angles."
    (step15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) := by euclid_apply (helper_1_45_step15 f g h m l (by euclid_assumption "" (show ∠ m:h:g + ∠ h:g:l = ∠ h:g:f + ∠ h:g:l; assumption)) (by euclid_assumption "" (show ∠ m:h:g + ∠ h:g:l = ∟ + ∟; assumption)))

  euclid_sentence "1.45.16"
    "Thus, $FG$ is straight-on to $GL$ [Prop.~1.14]."
    (step16 : FG = GL) := by euclid_apply (helper_1_45_step16 f g h k m l FG GL GH LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)) (by euclid_assumption "" (show ∠ h:g:f + ∠ h:g:l = ∟ + ∟; assumption)))

  -- @assumption_gap
  have step17_assumption1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH) := by euclid_apply (helper_1_45_step17_assumption1 f g k h FG KH FK GH (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)))
  -- @assumption_gap
  have step17_assumption2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by euclid_apply (helper_1_45_step17_assumption2 h m g l HM GL GH LM (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show ¬HM.intersectsLine GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))
  -- @assumption ("$FK$ is equal and parallel to $HG$", |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
  -- @assumption ("$HG$ to $ML$", |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
  euclid_sentence "1.45.17"
    "And since $FK$ is equal and parallel to $HG$ [Prop.~1.34], but also $HG$ to $ML$ [Prop.~1.34], $KF$ is thus also equal and parallel to $ML$ [Prop.~1.30]."
    (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM)) := by euclid_apply (helper_1_45_step17 f g k h m l FK FG GL GH LM KH (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by euclid_assumption "" (show FG = GL; assumption)) (by euclid_assumption "$FK$ is equal and parallel to $HG$" (show |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH); assumption)) (by euclid_assumption "$HG$ to $ML$" (show |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM); assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)))

  euclid_sentence "1.45.18"
    "And the straight-lines $KM$ and $FL$ join them."
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) := by euclid_apply (helper_1_45_step18 f g k h m l FG GL GH KH HM LM (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show FG = GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))

  euclid_sentence "1.45.19"
    "Thus, $KM$ and $FL$ are equal and parallel as well [Prop.~1.33]."
    (step19 : |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG)) := by euclid_apply (helper_1_45_step19 f g k h m l FK FG GL GH KH LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM; assumption)) (by euclid_assumption "" (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)))

  euclid_sentence "1.45.20"
    "Thus, $KFLM$ is a parallelogram."
    (step20 : formParallelogram f l k m FG KH FK LM) := by euclid_apply (helper_1_45_step20 f g k h m l FG GL GH KH HM FK LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show FG = GL; assumption)) (by euclid_assumption "" (show |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM; assumption)) (by euclid_assumption "" (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)))

  -- @assumption_valid
  have step21_assumption1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d := by assumption
  -- @assumption_valid
  have step21_assumption2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c := by assumption
  -- @assumption ("triangle $ABD$ is equal to parallelogram $FH$", Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
  -- @assumption ("$DBC$ to $GM$", Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
  euclid_sentence "1.45.21"
    "And since triangle $ABD$ is equal to parallelogram $FH$, and $DBC$ to $GM$, the whole rectilinear figure $ABCD$ is thus equal to the whole parallelogram $KFLM$."
    (step21 : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c) := by euclid_apply (helper_1_45_step21 a b c d f g k h m l FG KH FK GH LM (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ ∠k:h:g + ∠g:h:m = ∟ + ∟; assumption)) (by euclid_assumption "" (show |(h─g)| = |(m─l)| ∧ ¬GH.intersectsLine LM; assumption)) (by euclid_assumption "" (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)) (by euclid_assumption "" (show formParallelogram f l k m FG KH FK LM; assumption)) (by euclid_assumption "triangle $ABD$ is equal to parallelogram $FH$" (show Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d; assumption)) (by euclid_assumption "$DBC$ to $GM$" (show Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c; assumption)))

  use f, l, k, m, FG, KH, FK, LM
  have hangle : ∠ f:k:m = ∠ e₁:e₂:e₃ := by euclid_apply (helper_1_45_hangle e₁ e₂ e₃ f g k h m l FG KH FK GH (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show ∠ h:k:f = ∠ e₁:e₂:e₃; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ ∠ k:h:g + ∠ g:h:m = ∟ + ∟; assumption)) (by euclid_assumption "" (show |(f─k)| = |(h─g)| ∧ ¬FK.intersectsLine GH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG; assumption)))
  exact ⟨step20, hangle, step21⟩
  euclid_conclude_sentence "1.45.22"
    "Thus, the parallelogram $KFLM$, equal to the given rectilinear figure $ABCD$, has been constructed in the angle $FKM$, which is equal to the given (angle) $E$. (Which is) the very thing it was required to do."

end Elements.Book1
