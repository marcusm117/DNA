import SystemE
import Book.Prop05
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_9_step9_hfab (a b c d e f : Point) (AB AC DE EF : Line)
    (ha_on_AB : a.onLine AB) (hb_on_AB : b.onLine AB) (hd_on_AB : d.onLine AB)
    (ha_on_AC : a.onLine AC) (hc_on_AC : c.onLine AC)
    (hd_on_DE : d.onLine DE) (he_on_DE : e.onLine DE)
    (he_on_EF : e.onLine EF) (hf_on_EF : f.onLine EF)
    (hf_off_DE : ¬f.onLine DE) (ha_off_DE : ¬a.onLine DE)
    (hf_opp_DE : ¬f.sameSide a DE)
    (hAB_ne_AC : AB ≠ AC)
    (hbtw_adb : between a d b) (hbtw_aec : between a e c)
    (hAD_eq_AE : |(a─d)| = |(a─e)|)
    (hFD_eq_DE : |(f─d)| = |(d─e)|)
    (hFE_eq_DE : |(f─e)| = |(d─e)|) :
    ¬f.onLine AB := by
  intro hf_on_AB
  have hFD_eq_FE : |(f─d)| = |(f─e)| := by linarith
  euclid_apply (proposition_5' f d e AB DE EF)
  euclid_apply (proposition_5 a d e b c AB DE AC)
  euclid_finish

end Elements.Book1
