import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_8_step3 (b c k q : Point) (AB AE BL CH MN OP : Line)
    (h_c_ch : c.onLine CH) (h_ch_ae : ¬(CH.intersectsLine AE))
    (h_b_bl : b.onLine BL) (h_bl_ae : ¬(BL.intersectsLine AE))
    (h_k_mn : k.onLine MN) (h_mn_ab : ¬(MN.intersectsLine AB))
    (h_q_op : q.onLine OP) (h_op_ab : ¬(OP.intersectsLine AB)) :
    c.onLine CH ∧ ¬(CH.intersectsLine AE) ∧ b.onLine BL ∧ ¬(BL.intersectsLine AE) ∧
      k.onLine MN ∧ ¬(MN.intersectsLine AB) ∧ q.onLine OP ∧ ¬(OP.intersectsLine AB) := by
  exact ⟨h_c_ch, h_ch_ae, h_b_bl, h_bl_ae, h_k_mn, h_mn_ab, h_q_op, h_op_ab⟩

end Elements.Book2
