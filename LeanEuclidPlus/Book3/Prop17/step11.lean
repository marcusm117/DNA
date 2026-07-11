import SystemE
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_17_step11 (a b d e f : Point) (AE EF AB DF : Line)
    (he_onAE : e.onLine AE)
    (ha_onAE : a.onLine AE)
    (hd_onAE : d.onLine AE)
    (he_onEF : e.onLine EF)
    (hb_onEF : b.onLine EF)
    (hf_onEF : f.onLine EF)
    (ha_onAB : a.onLine AB)
    (hb_onAB : b.onLine AB)
    (hd_onDF : d.onLine DF)
    (hf_onDF : f.onLine DF)
    (hane : a ≠ e)
    (habne : a ≠ b)
    (hefne : e ≠ f)
    (hf_notAE : ¬f.onLine AE)
    (hbetween_ade : between a d e)
    (hbetween_ebf : between e b f)
    (step9 : |(a─e)| = |(f─e)| ∧ |(e─b)| = |(e─d)|)
    (step10 : ∠ a:e:b = ∠ f:e:d) :
    |(d─f)| = |(a─b)| := by
  have h_be : b ≠ e := (between_symm e b f hbetween_ebf).2.1.symm
  have h_de : d ≠ e := (between_symm e d a (between_symm a d e hbetween_ade).1).2.1.symm
  have htri1 : formTriangle e a b AE AB EF := by euclid_finish
  have htri2 : formTriangle e f d EF DF AE := by euclid_finish
  have h_ea_ef : |(e─a)| = |(e─f)| := by linarith [segment_symmetric e a, segment_symmetric f e]
  have h4 := proposition_4 e a b e f d AE AB EF EF DF AE
    ⟨htri1, htri2, h_ea_ef, step9.2, step10⟩
  linarith [segment_symmetric d f, h4.1, segment_symmetric a b]

end Elements.Book3
