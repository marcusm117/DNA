import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: parallelogram HGLE = formParallelogram h g l e DG CE KM EF. (Mirror of Prop06 step7_par2
   under relabel BG→DG.) def a b c d AB CD AC BD: a=h,b=g on DG; c=l,d=e on CE; a=h,c=l on KM;
   b=g,d=e on EF. sameSide h.sameSide l EF (step6_par2_ss); g ≠ e from g ∈ DG, ¬e ∈ DG (step6_eoffdg).
   Parallels DG∥CE, KM∥EF in hand. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_par2 (e g h l : Point) (DG CE KM EF : Line)
    (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hlCE : l.onLine CE) (heCE : e.onLine CE)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (heoffDG : ¬(e.onLine DG)) (hsshl : h.sameSide l EF)
    (hDGCE : ¬(DG.intersectsLine CE)) (hKMEF : ¬(KM.intersectsLine EF)) :
    formParallelogram h g l e DG CE KM EF := by
  euclid_intros
  have hge : g ≠ e := fun heq => heoffDG (heq ▸ hgDG)
  euclid_finish

end Elements.Book2
