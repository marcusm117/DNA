import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_20_step7_subE
  (a b c e f : Point) (AEF EC : Line)
  (h_e_AEF : e.onLine AEF) (h_f_AEF : f.onLine AEF)
  (h_e_EC : e.onLine EC) (h_c_EC : c.onLine EC)
  (h_enf : e ≠ f) (h_enc : e ≠ c)
  (h_b_off_AEF : ¬ b.onLine AEF) (h_b_off_EC : ¬ b.onLine EC) (h_AEFneEC : AEF ≠ EC)
  (hf_b_EC : f.sameSide b EC) (hc_b_AEF : c.sameSide b AEF)
  : ∠ f:e:c = ∠ f:e:b + ∠ b:e:c := by
  euclid_apply (sum_angles_onlyif e f c b AEF EC)
  euclid_finish

end Elements.Book3
