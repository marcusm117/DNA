import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step24_ehf (a b d e f h : Point) (AB CH EF : Line)
    (h_a_ab : a.onLine AB) (h_abd : between a b d) (h_d_ab : d.onLine AB)
    (h_e_ef : e.onLine EF) (h_f_ef : f.onLine EF) (h_h_ef : h.onLine EF)
    (h_ef_eq : |(e─f)| = |(a─d)|)
    (h_h_ch : h.onLine CH)
    (h_each : e.sameSide a CH) (h_fdch : f.sameSide d CH)
    (h_efopp : ¬(e.sameSide f CH)) :
    between e h f := by
  have h_e_off_ch : ¬(e.onLine CH) := by
    euclid_finish
  have h_f_off_ch : ¬(f.onLine CH) := by
    euclid_finish
  have hne_ch_ef : CH ≠ EF := fun heq => h_e_off_ch (heq.symm ▸ h_e_ef)
  have h_ef_ne : e ≠ f := by
    euclid_finish
  have h_e_ne_h : e ≠ h := fun heq => h_e_off_ch (heq ▸ h_h_ch)
  have h_f_ne_h : f ≠ h := fun heq => h_f_off_ch (heq ▸ h_h_ch)
  euclid_apply (pasch_4 e h f CH EF)
  euclid_finish

end Elements.Book2
