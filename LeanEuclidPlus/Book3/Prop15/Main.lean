import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop15.step1
import Book3.Prop15.step2
import Book3.Prop15.step3
import Book3.Prop15.step4
import Book3.Prop15.step5
import Book3.Prop15.step6
import Book3.Prop15.step7
import Book3.Prop15.step8
import Book3.Prop15.step9
import Book3.Prop15.step10
import Book3.Prop15.step11
import Book3.Prop15.step12
import Book3.Prop15.step13
import Book3.Prop15.step14
import Book3.Prop15.hlines
import Book3.Prop15.hstep3
import Book3.Prop15.hstep4_aux
import Book3.Prop15.hstep4_pts
import Book3.Prop15.step11_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_15 : ∀ (a b c d e f g h k : Point) (ABCD : Circle) (BC FG : Line),
  e.isCentre ABCD ∧
  a.onCircle ABCD ∧ d.onCircle ABCD ∧ between a e d ∧
  b.onCircle ABCD ∧ c.onCircle ABCD ∧ distinctPointsOnLine b c BC ∧
  f.onCircle ABCD ∧ g.onCircle ABCD ∧ distinctPointsOnLine f g FG ∧
  h.onLine BC ∧ ∠ e:h:b = ∟ ∧ e ≠ h ∧ h ≠ b ∧
  k.onLine FG ∧ ∠ e:k:f = ∟ ∧ k ≠ f ∧
  |(e─h)| < |(e─k)| →
  |(a─d)| > |(b─c)| ∧ |(b─c)| > |(f─g)| :=
by
  euclid_intros
  euclid_intro_sentence "3.15.0"
    "In a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away. Let $ABCD$ be a circle, and let $AD$ be its diameter, and $E$ (its) center. And let $BC$ be nearer to the diameter $AD$,$^\\dag$ and $FG$ further away. I say that $AD$ is the greatest (straight-line), and $BC$ (is) greater than $FG$."

  have heh : e ≠ h := by assumption
  have hkf : k ≠ f := by assumption
  have hhb : h ≠ b := by assumption

  have hlines : ∃ EH EK : Line, distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK := by euclid_apply (helper_3_15_hlines e h k (by euclid_assumption "" (show e ≠ h; assumption)) (by euclid_assumption "" (show |(e─h)| < |(e─k)|; assumption)))
  obtain ⟨EH, EK, hEH, hEK⟩ := hlines
  euclid_sentence "3.15.1"
    "For let $EH$ and $EK$ be drawn from the center $E$, at right-angles to $BC$ and $FG$ (respectively) [Prop.~1.12]."
    (step1 : distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK ∧ ∠ e:h:b = ∟ ∧ ∠ e:k:f = ∟) := by euclid_apply (helper_3_15_step1 e h k b c f g EH EK BC FG (by euclid_assumption "" (show distinctPointsOnLine e h EH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show h.onLine BC; assumption)) (by euclid_assumption "" (show ∠ e:h:b = ∟; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show e ≠ h; assumption)) (by euclid_assumption "" (show k ≠ f; assumption)) (by euclid_assumption "" (show h ≠ b; assumption)))

  -- @assumption_valid
  have step2_assumption1 : |(e─h)| < |(e─k)| := by assumption
  -- @assumption ("$BC$ is nearer to the center, and $FG$ further away", |(e─h)| < |(e─k)|)
  euclid_sentence "3.15.2"
     "And since $BC$ is nearer to the center, and $FG$ further away, $EK$ (is) thus greater than $EH$ [Def.~3.5]."
    (step2 : |(e─k)| > |(e─h)|) := by euclid_apply (helper_3_15_step2 e h k (by euclid_assumption "$BC$ is nearer to the center, and $FG$ further away" (show |(e─h)| < |(e─k)|; assumption)))

  have hstep3 : ∃ l : Point, between e l k ∧ |(e─l)| = |(e─h)| := by euclid_apply (helper_3_15_hstep3 e h k EH EK (by euclid_assumption "" (show distinctPointsOnLine e h EH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show |(e─k)| > |(e─h)|; assumption)))
  obtain ⟨l, hl_betw, hl_eq⟩ := hstep3
  euclid_sentence "3.15.3"
    "Let $EL$ be made equal to $EH$ [Prop.~1.3]."
    (step3 : |(e─l)| = |(e─h)|) := by euclid_apply (helper_3_15_step3 e h k l EH EK (by euclid_assumption "" (show distinctPointsOnLine e h EH; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show |(e─k)| > |(e─h)|; assumption)) (by euclid_assumption "" (show |(e─l)| = |(e─h)|; assumption)))

  have hstep4_aux : ∃ (m0 : Point) (MN : Line),
      ¬(m0.onLine EK) ∧ ∠ e:l:m0 = ∟ ∧ distinctPointsOnLine l m0 MN := by euclid_apply (helper_3_15_hstep4_aux e k l EK (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show between e l k; assumption)))
  obtain ⟨m0, MN, hm0_off, hm0_perp, hMN⟩ := hstep4_aux
  have hstep4_pts : ∃ m n : Point,
      m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟ ∧
      m.onLine MN ∧ n.onLine MN := by euclid_apply (helper_3_15_hstep4_pts e k l h f m0 ABCD FG EK MN (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show |(e─l)| = |(e─h)|; assumption)) (by euclid_assumption "" (show |(e─h)| < |(e─k)|; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show ¬m0.onLine EK; assumption)) (by euclid_assumption "" (show ∠ e:l:m0 = ∟; assumption)) (by euclid_assumption "" (show distinctPointsOnLine l m0 MN; assumption)))
  obtain ⟨m, n, hm_on, hn_on, hbetw, hperp, hm_MN, hn_MN⟩ := hstep4_pts
  euclid_sentence "3.15.4"
    "And $LM$ being drawn through $L$, at right-angles to $EK$ [Prop.~1.11], let it be drawn through to $N$."
    (step4 : m.onCircle ABCD ∧ n.onCircle ABCD ∧ between m l n ∧ ∠ m:l:e = ∟) := by euclid_apply (helper_3_15_step4 m n l e k ABCD EK (by euclid_assumption "" (show distinctPointsOnLine e k EK; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)))

  euclid_apply (line_from_points m e) as ME
  euclid_apply (line_from_points e n) as EN
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points e g) as EG
  euclid_sentence "3.15.5"
    "And let $ME$, $EN$, $FE$, and $EG$ be joined."
    (step5 : distinctPointsOnLine m e ME ∧ distinctPointsOnLine e n EN ∧ distinctPointsOnLine f e FE ∧ distinctPointsOnLine e g EG) := by euclid_apply (helper_3_15_step5 m n e f g ABCD ME EN FE EG (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine EN; assumption)) (by euclid_assumption "" (show n.onLine EN; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)))

  -- @assumption_valid
  have step6_assumption1 : |(e─h)| = |(e─l)| := by linarith
  -- @assumption ("$EH$ is equal to $EL$", |(e─h)| = |(e─l)|)
  euclid_sentence "3.15.6"
    "And since $EH$ is equal to $EL$, $BC$ is also equal to $MN$ [Prop.~3.14]."
    (step6 : |(b─c)| = |(m─n)|) := by euclid_apply (helper_3_15_step6 b c m n e h l ABCD BC MN EH (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show b.onCircle ABCD; assumption)) (by euclid_assumption "" (show c.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show h.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show e.onLine EH; assumption)) (by euclid_assumption "" (show h.onLine EH; assumption)) (by euclid_assumption "" (show e ≠ h; assumption)) (by euclid_assumption "" (show ∠ e:h:b = ∟; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "$EH$ is equal to $EL$" (show |(e─h)| = |(e─l)|; assumption)))

  -- @assumption_valid
  have step7_assumption1 : |(a─e)| = |(m─e)| ∧ |(e─d)| = |(e─n)| := by euclid_finish
  -- @assumption ("$AE$ is equal to $EM$, and $ED$ to $EN$", |(a─e)| = |(m─e)| ∧ |(e─d)| = |(e─n)|)
  euclid_sentence "3.15.7"
    "Again, since $AE$ is equal to $EM$, and $ED$ to $EN$, $AD$ is thus equal to $ME$ and $EN$."
    (step7 : |(a─d)| = |(m─e)| + |(e─n)|) := by euclid_apply (helper_3_15_step7 a d e m n (by euclid_assumption "" (show between a e d; assumption)) (by euclid_assumption "$AE$ is equal to $EM$, and $ED$ to $EN$" (show |(a─e)| = |(m─e)| ∧ |(e─d)| = |(e─n)|; assumption)))

  euclid_sentence "3.15.8"
    "But, $ME$ and $EN$ is greater than $MN$ [Prop.~1.20] [also $AD$ is greater than $MN$],"
    (step8 : |(m─e)| + |(e─n)| > |(m─n)|) := by euclid_apply (helper_3_15_step8 m e n l m0 k ABCD ME MN EN EK (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show e.onLine EN; assumption)) (by euclid_assumption "" (show n.onLine EN; assumption)) (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show m0.onLine MN; assumption)) (by euclid_assumption "" (show ¬m0.onLine EK; assumption)))

  -- orchestrator-restatement: step9 flips = from step6 (|(b─c)|=|(m─n)|); Euclid writes both, faithful to keep
  euclid_sentence "3.15.9"
    "and $MN$ (is) equal to $BC$."
    (step9 : |(m─n)| = |(b─c)|) := by euclid_apply (helper_3_15_step9 b c m n (by euclid_assumption "" (show |(b─c)| = |(m─n)|; assumption)))

  euclid_sentence "3.15.10"
    "Thus, $AD$ is greater than $BC$."
    (step10 : |(a─d)| > |(b─c)|) := by euclid_apply (helper_3_15_step10 a d b c m e n (by euclid_assumption "" (show |(a─d)| = |(m─e)| + |(e─n)|; assumption)) (by euclid_assumption "" (show |(m─e)| + |(e─n)| > |(m─n)|; assumption)) (by euclid_assumption "" (show |(m─n)| = |(b─c)|; assumption)))

  -- @assumption_valid
  have step11_assumption1 : |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)| := by euclid_finish
  -- @assumption_gap
  have step11_assumption2 : ∠ m:e:n > ∠ f:e:g := by euclid_apply (helper_3_15_step11_assumption2 e f g l k m n m0 h ABCD EK FG MN ME EN FE EG (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine EN; assumption)) (by euclid_assumption "" (show n.onLine EN; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show m0.onLine MN; assumption)) (by euclid_assumption "" (show ¬m0.onLine EK; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show |(e─h)| < |(e─k)|; assumption)) (by euclid_assumption "" (show |(e─l)| = |(e─h)|; assumption)) (by euclid_assumption "" (show |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show k ≠ f; assumption)))
  -- @assumption ("the two (straight-lines) $ME$, $EN$ are equal to the two (straight-lines) $FE$, $EG$ (respectively)", |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|)
  -- @assumption ("angle $MEN$ [is] greater than angle $FEG$", ∠ m:e:n > ∠ f:e:g)
  euclid_sentence "3.15.11"
    "And since the two (straight-lines) $ME$, $EN$ are equal to the two (straight-lines) $FE$, $EG$ (respectively), and angle $MEN$ [is] greater than angle $FEG$,$^\\ddag$ the base $MN$ is thus greater than the base $FG$ [Prop.~1.24]."
    (step11 : |(m─n)| > |(f─g)|) := by euclid_apply (helper_3_15_step11 e m n f g l k ME MN EN FE FG EG (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show e.onLine EN; assumption)) (by euclid_assumption "" (show n.onLine EN; assumption)) (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show e ≠ k; assumption)) (by euclid_assumption "" (show k ≠ f; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "the two (straight-lines) $ME$, $EN$ are equal to the two (straight-lines) $FE$, $EG$ (respectively)" (show |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|; assumption)) (by euclid_assumption "angle $MEN$ [is] greater than angle $FEG$" (show ∠ m:e:n > ∠ f:e:g; assumption)))

  -- @assumption_valid
  have step12_assumption1 : |(m─n)| = |(b─c)| := by assumption
  -- @assumption ("$MN$ was shown (to be) equal to $BC$", |(m─n)| = |(b─c)|)
  euclid_sentence "3.15.12"
    "But, $MN$ was shown (to be) equal to $BC$ [(so) $BC$ is also greater than $FG$]."
    (step12 : |(b─c)| > |(f─g)|) := by euclid_apply (helper_3_15_step12 b c f g m n (by euclid_assumption "" (show |(m─n)| > |(f─g)|; assumption)) (by euclid_assumption "$MN$ was shown (to be) equal to $BC$" (show |(m─n)| = |(b─c)|; assumption)))

  euclid_sentence "3.15.13"
    "Thus, the diameter $AD$ (is) the greatest (straight-line),"
    (step13 : |(a─d)| > |(b─c)|) := by euclid_apply (helper_3_15_step13 a b c d (by euclid_assumption "" (show |(a─d)| > |(b─c)|; assumption)))

  -- orchestrator-restatement: step14 restates step12 as part-2 summary; faithful (Euclid writes both)
  euclid_sentence "3.15.14"
    "and $BC$ (is) greater than $FG$."
    (step14 : |(b─c)| > |(f─g)|) := by euclid_apply (helper_3_15_step14 b c f g (by euclid_assumption "" (show |(b─c)| > |(f─g)|; assumption)))

  exact ⟨step13, step14⟩
  euclid_conclude_sentence "3.15.15"
    "Thus, in a circle, a diameter (is) the greatest (straight-line), and for the others, a (straight-line) nearer to the center is always greater than one further away. (Which is) the very thing it was required to show."

end Elements.Book3
