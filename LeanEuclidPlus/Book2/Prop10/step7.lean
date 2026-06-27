import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step7 (2.10.7): FEB + EFD < two right-angles. ray e→b is interior to ∠FEC (b between c,d on the
-- base, e above), so ∠f:e:b < ∠c:e:f; add step6 (∠c:e:f + ∠e:f:d = ∟+∟). Rich figure context lets
-- euclid_finish derive the interior ordering.
theorem helper_2_10_step7
  (a b c d e e0 e1 f : Point) (AD CE EF FD EB : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB)
  (hf_fd : f.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE)
  (hstep6 : ∠ c:e:f + ∠ e:f:d = ∟ + ∟) :
  ∠ f:e:b + ∠ e:f:d < ∟ + ∟ := by
  euclid_finish

end Elements.Book2
