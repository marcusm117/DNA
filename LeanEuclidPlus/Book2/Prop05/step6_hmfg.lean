import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: complement parallelogram HMFG = formParallelogram h m g f KM EF DG BF. (Mirror of Prop06
   step7_hmfg under relabel BG→DG, DF→BF.) def a b c d AB CD AC BD: a=h,b=m on KM; c=g,d=f on EF;
   a=h,c=g on DG; b=m,d=f on BF. sameSide h.sameSide g BF (step6_hmfg_ss); m ≠ f from m ∈ KM, ¬f ∈ KM
   (step6_foffkm). Parallels KM∥EF, DG∥BF in hand. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_hmfg (f g h m : Point) (KM EF DG BF : Line)
    (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hmBF : m.onLine BF) (hfBF : f.onLine BF)
    (hfoffKM : ¬(f.onLine KM)) (hsshg : h.sameSide g BF)
    (hKMEF : ¬(KM.intersectsLine EF)) (hDGBF : ¬(DG.intersectsLine BF)) :
    formParallelogram h m g f KM EF DG BF := by
  euclid_intros
  have hmf : m ≠ f := fun heq => hfoffKM (heq ▸ hmKM)
  euclid_finish

end Elements.Book2
