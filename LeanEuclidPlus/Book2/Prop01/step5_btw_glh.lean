import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: the foot l of EL on GH lies between the feet g (of BF) and h (of CH).
   l ∈ EL ∩ GH; g and h are distinct points of GH. g and h are on OPPOSITE sides of EL:
   g shares b's side (b.sameSide g EL), h shares c's side (c.sameSide h EL), and b,c are on
   opposite sides of EL because e (between b and c on BC) lies on EL (pasch_3). Then pasch_4
   on g, l, h across EL and GH gives between g l h. -/
theorem helper_2_1_step5_btw_glh (b c d e g h l : Point) (BC GH EL : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hlGH : l.onLine GH)
    (heEL : e.onLine EL) (hlEL : l.onLine EL)
    (hssbg : b.sameSide g EL) (hsschc : c.sameSide h EL) :
    between g l h := by
  euclid_intros
  -- b and c are on opposite sides of EL, since e (on EL) is between b and c on BC
  have hbec : between b e c := by euclid_finish
  euclid_apply (pasch_3 b e c EL)
  -- so g (b's side) and h (c's side) are on opposite sides of EL
  euclid_apply (pasch_4 g l h EL GH)
  euclid_finish

end Elements.Book2
