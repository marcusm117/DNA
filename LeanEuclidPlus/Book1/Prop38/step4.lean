import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step4
  (a b c d e f g h : Point)
  (AD BF AB AC DE BG FH : Line)
  (ha_AD : a.onLine AD) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
  (hb_BF : b.onLine BF) (hc_BF : c.onLine BF) (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
  (hAB_BF : AB ≠ BF)
  (hd_AD : d.onLine AD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
  (he_BF : e.onLine BF) (hf_BF : f.onLine BF) (hDE_BF : DE ≠ BF)
  (hb_BG : b.onLine BG) (hg_BG : g.onLine BG) (hg_AD : g.onLine AD) (hBG_AC : ¬BG.intersectsLine AC)
  (hf_FH : f.onLine FH) (hh_FH : h.onLine FH) (hh_AD : h.onLine AD) (hFH_DE : ¬FH.intersectsLine DE)
  (hbcf : between b c f) (hbef : between b e f)
  (hAD_BF : ¬AD.intersectsLine BF)
  : formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF := by
  have ha_off_BF : ¬a.onLine BF := by euclid_finish
  have hd_off_BF : ¬d.onLine BF := by euclid_finish
  have hg_ss_a : g.sameSide a BF :=
    sameSide_of_parallel' g a a AD BF hg_AD ha_AD ha_AD ha_off_BF hAD_BF
  have hd_ss_h : d.sameSide h BF :=
    sameSide_of_parallel' d h d AD BF hd_AD hh_AD hd_AD hd_off_BF hAD_BF
  exact ⟨⟨hg_BG, hb_BG, ha_AC, hc_AC, hg_AD, ha_AD,
          ⟨hb_BF, hc_BF, by euclid_finish⟩, hg_ss_a, hBG_AC, hAD_BF⟩,
         ⟨hd_DE, he_DE, hh_FH, hf_FH, hd_AD, hh_AD,
          ⟨he_BF, hf_BF, by euclid_finish⟩, hd_ss_h, by euclid_finish, hAD_BF⟩⟩

end Elements.Book1
