import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step8 (2.10.8): Post 5 — EB and FD meet. TEST 2: rich figure context + euclid_finish.
theorem helper_2_10_step8
  (a b c d e e0 e1 f : Point) (AD CE EF FD EB : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hf_fd : f.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep6 : ∠ c:e:f + ∠ e:f:d = ∟ + ∟)
  (hstep7 : ∠ f:e:b + ∠ e:f:d < ∟ + ∟) :
  EB.intersectsLine FD := by
  euclid_finish

end Elements.Book2
