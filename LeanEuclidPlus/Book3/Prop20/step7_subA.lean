import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_subA
  (a b c e : Point) (AEF AC : Line)
  (h_a_AEF : a.onLine AEF) (h_e_AEF : e.onLine AEF)
  (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC)
  (h_ane_e : a ≠ e) (h_ane_c : a ≠ c)
  (h_b_off_AEF : ¬ b.onLine AEF) (h_b_off_AC : ¬ b.onLine AC) (h_AEFneAC : AEF ≠ AC)
  (he_b_AC : e.sameSide b AC) (hc_b_AEF : c.sameSide b AEF)
  : ∠ e:a:c = ∠ e:a:b + ∠ b:a:c := by
  euclid_apply (sum_angles_onlyif a e c b AEF AC)
  euclid_finish

end Elements.Book3
