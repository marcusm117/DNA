import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.16 sub: e, b, g are collinear on EB (b = EB ∩ AD), with e above AD (on CE ⊥ AD) and
   g below AD (on FD ∥ CE, the EB-meeting point). Hence e, g on opposite sides of AD and the
   crossing point b lies between them: between e b g. Focused figure context (mirrors step8). -/
set_option systemE.solverTime 30 in
theorem helper_2_10_step16_beg
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE) :
  between e b g := by
  euclid_finish

end Elements.Book2
