import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_17_step12 (a b d e f : Point) (AE EF DF AB : Line)
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
    (step10 : ∠ a:e:b = ∠ f:e:d) :
    Triangle.area △ d:e:f = Triangle.area △ e:b:a := by
  euclid_finish

end Elements.Book3
