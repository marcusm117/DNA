import SystemE
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step13 (a b d e f : Point) (AE EF DF AB : Line)
    (he_onAE : e.onLine AE) (ha_onAE : a.onLine AE) (hd_onAE : d.onLine AE)
    (he_onEF : e.onLine EF) (hb_onEF : b.onLine EF) (hf_onEF : f.onLine EF)
    (hd_onDF : d.onLine DF) (hf_onDF : f.onLine DF)
    (ha_onAB : a.onLine AB) (hb_onAB : b.onLine AB)
    (hane : a ≠ e) (habne : a ≠ b) (hefne : e ≠ f) (hdfne : d ≠ f)
    (hf_notAE : ¬f.onLine AE)
    (hbetween_ade : between a d e)
    (hbetween_ebf : between e b f)
    (step7 : |(e─a)| = |(e─f)|)
    (step8 : |(e─d)| = |(e─b)|)
    (step11 : |(d─f)| = |(a─b)|) :
    ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b := by
  have htri1 : formTriangle e d f AE DF EF := by euclid_finish
  have htri2 : formTriangle e b a EF AB AE := by euclid_finish
  have h4 : |(d─f)| = |(b─a)| ∧ ∠ e:d:f = ∠ e:b:a ∧ ∠ e:f:d = ∠ e:a:b := by
    euclid_apply (Elements.Book1.proposition_4 e d f e b a AE DF EF EF AB AE
      ⟨htri1, htri2, step8, step7.symm, by euclid_finish⟩)
  exact ⟨h4.2.1, h4.2.2⟩

end Elements.Book3
