import SystemE
import Helpers.SameSide
import Book.Prop36
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_38_step5
    (a b c d e f g h : Point)
    (AD BF AB AC DE BG FH : Line)
    (ha_AD : a.onLine AD) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BF : b.onLine BF) (hc_BF : c.onLine BF)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hAB_BF : AB ≠ BF) (hBF_AC : BF ≠ AC)
    (hd_AD : d.onLine AD) (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (he_BF : e.onLine BF) (hf_BF : f.onLine BF) (hDE_BF : DE ≠ BF)
    (hb_BG : b.onLine BG) (hg_BG : g.onLine BG) (hg_AD : g.onLine AD)
    (hBG_AC : ¬BG.intersectsLine AC)
    (hf_FH : f.onLine FH) (hh_FH : h.onLine FH) (hh_AD : h.onLine AD)
    (hFH_DE : ¬FH.intersectsLine DE)
    (hbcf : between b c f) (hbef : between b e f)
    (hAD_BF : ¬AD.intersectsLine BF)
    (hstep4 : formParallelogram g b a c BG AC AD BF ∧ formParallelogram d e h f DE FH AD BF)
    (hassump1 : |(b─c)| = |(e─f)| ∧ ¬(AD.intersectsLine BF))
    : Triangle.area △ g:b:c + Triangle.area △ g:c:a =
      Triangle.area △ d:e:f + Triangle.area △ d:f:h := by
  -- Off-line facts
  have ha_off_BF : ¬a.onLine BF := by euclid_finish
  have hb_off_AC : ¬b.onLine AC := by euclid_finish
  -- a ≠ c: a ∉ BF, c ∈ BF
  have hac : a ≠ c := fun heq => ha_off_BF (heq ▸ hc_BF)
  -- h ≠ f: h ∈ AD, f ∈ BF; AD ≠ BF from a ∈ AD, a ∉ BF
  have hAD_ne_BF : AD ≠ BF := fun heq => ha_off_BF (heq ▸ ha_AD)
  have hhf : h ≠ f := fun heq =>
    hAD_BF (intersection_lines_common_point f AD BF ⟨heq ▸ hh_AD, hf_BF, hAD_ne_BF⟩)
  -- g.sameSide b AC: both on BG ∥ AC, b ∉ AC
  have hg_ss_b : g.sameSide b AC :=
    sameSide_of_parallel' g b b BG AC hg_BG hb_BG hb_BG hb_off_AC hBG_AC
  -- formParallelogram g a b c AD BF BG AC (re-oriented for proposition_36')
  have hpgram1 : formParallelogram g a b c AD BF BG AC :=
    ⟨hg_AD, ha_AD, hb_BF, hc_BF, hg_BG, hb_BG, ⟨ha_AC, hc_AC, hac⟩, hg_ss_b, hAD_BF, hBG_AC⟩
  -- d ∉ FH: d ∈ DE, ¬FH.intersectsLine DE, derive FH ≠ DE from the context
  have hd_off_FH : ¬d.onLine FH := by euclid_finish
  -- ¬DE.intersectsLine FH from ¬FH.intersectsLine DE
  have hDE_FH : ¬DE.intersectsLine FH := fun h => hFH_DE (intersection_symm DE FH h)
  -- d.sameSide e FH: both on DE ∥ FH, d ∉ FH
  have hd_ss_e : d.sameSide e FH :=
    sameSide_of_parallel' d e d DE FH hd_DE he_DE hd_DE hd_off_FH hDE_FH
  -- formParallelogram d h e f AD BF DE FH (re-oriented for proposition_36')
  have hpgram2 : formParallelogram d h e f AD BF DE FH :=
    ⟨hd_AD, hh_AD, he_BF, hf_BF, hd_DE, he_DE, ⟨hh_FH, hf_FH, hhf⟩, hd_ss_e, hAD_BF, hDE_FH⟩
  -- proposition_36' gives: △g:b:a + △a:b:c = △d:e:h + △h:e:f
  have heq36 : Triangle.area △ g:b:a + Triangle.area △ a:b:c =
               Triangle.area △ d:e:h + Triangle.area △ h:e:f := by
    euclid_apply (proposition_36' g b c a d e f h AD BF BG AC DE FH ⟨hpgram1, hpgram2, hassump1.1⟩)
  -- parallelogram_area on step4.1: △g:a:c + △g:c:b = △b:g:a + △b:a:c
  have heq_pa1 := parallelogram_area g b a c BG AC AD BF hstep4.1
  -- parallelogram_area on step4.2: △d:h:f + △d:f:e = △e:d:h + △e:h:f
  have heq_pa2 := parallelogram_area d e h f DE FH AD BF hstep4.2
  linarith [area_symm_2 g a c, area_symm_2 g c b,
            area_symm_2 b g a, area_symm_1 b a g,
            area_symm_2 a b c, area_symm_1 a c b,
            area_symm_2 d h f, area_symm_2 d f e,
            area_symm_2 e d h, area_symm_1 e h d,
            area_symm_1 e h f, area_symm_1 f e h, area_symm_2 h f e]

end Elements.Book1
