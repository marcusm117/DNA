import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- ∠a:e:b = ∠f:e:d via equal_angles: vertex e, arms (a,d) on AE same side, (b,f) on EF same side.
-- Then angle_symm swaps d and f.
theorem helper_3_17_step10 (a b d e f : Point) (AE EF : Line)
    (ha_onAE : a.onLine AE)
    (he_onAE : e.onLine AE)
    (hd_onAE : d.onLine AE)
    (he_onEF : e.onLine EF)
    (hb_onEF : b.onLine EF)
    (hf_onEF : f.onLine EF)
    (hbetween_ade : between a d e)
    (hbetween_ebf : between e b f)
    (hane : a ≠ e)
    (hefne : e ≠ f) :
    ∠ a:e:b = ∠ f:e:d := by
  have h_de : d ≠ e := by
    have := (between_symm e d a (between_symm a d e hbetween_ade).1).2.1
    exact this.symm
  have h_be : b ≠ e := (between_symm e b f hbetween_ebf).2.1.symm
  have h_naed : ¬between a e d := by euclid_finish
  have h_nbef : ¬between b e f := (between_symm e b f hbetween_ebf).2.2.2
  have h_aeb_def : ∠ a:e:b = ∠ d:e:f :=
    equal_angles e a d b f AE EF
      ⟨he_onAE, ha_onAE, hd_onAE, he_onEF, hb_onEF, hf_onEF,
       hane, h_de, h_be, hefne.symm, h_naed, h_nbef⟩
  exact h_aeb_def.trans (angle_symm d e f ⟨h_de, hefne⟩)

end Elements.Book3
