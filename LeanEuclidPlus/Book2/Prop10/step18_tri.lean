import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.10.18 sub: g, b, d form a triangle (EB = g─b, AD = b─d, FD = g─d). formTriangle needs the three
   lines pairwise distinct; the figure anchors (e off AD on EB, b on AD not FD, d on FD not EB) let
   euclid_finish derive them. -/
theorem helper_2_10_step18_tri
  (a b c d e e0 e1 f g : Point) (AD CE EB EF FD : Line)
  (hab_a : a.onLine AD) (hab_c : c.onLine AD) (hab_b : b.onLine AD) (hab_d : d.onLine AD)
  (hacb : between a c b) (habd : between a b d)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE)
  (hne0 : ¬e0.onLine AD) (hbte : between c e e1) (hperp : ∠ a:c:e0 = ∟)
  (he_eb : e.onLine EB) (hb_eb : b.onLine EB) (hg_eb : g.onLine EB)
  (hg_fd : g.onLine FD) (hd_fd : d.onLine FD)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hf_fd : f.onLine FD)
  (hEFAD : ¬EF.intersectsLine AD) (hFDCE : ¬FD.intersectsLine CE) :
  formTriangle g b d EB AD FD := by
  euclid_finish

end Elements.Book2
