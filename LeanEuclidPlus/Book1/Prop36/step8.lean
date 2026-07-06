import SystemE
import Book1.Prop34.variants
import Book1.Prop35.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
  (h_e_AH : e.onLine AH) (h_h_AH : h.onLine AH)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_f_BG : f.onLine BG) (h_g_BG : g.onLine BG)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
  (h_h_HG : h.onLine HG) (h_g_HG : g.onLine HG)
  (h_h_ne_g : h ≠ g)
  (h_ss_ef_HG : e.sameSide f HG)
  (h_par : ¬AH.intersectsLine BG)
  (h_ef_ne_hg : ¬EF.intersectsLine HG)
  (h_b_BE : b.onLine BE) (h_e_BE : e.onLine BE)
  (h_c_CH : c.onLine CH) (h_h_CH : h.onLine CH)
  (h_step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
  (h_step5 : |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH)
  (h_step6 : formParallelogram e h b c AH BG BE CH) :
  Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  have h_pgram2 : formParallelogram e h f g AH BG EF HG :=
    ⟨h_e_AH, h_h_AH, h_f_BG, h_g_BG, h_e_EF, h_f_EF,
     ⟨h_h_HG, h_g_HG, h_h_ne_g⟩, h_ss_ef_HG, h_par, h_ef_ne_hg⟩
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_finish

end Elements.Book1
