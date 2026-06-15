import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.9 sub: the rectangle AM = formParallelogram a d k m AB KM AK DF. def a b c d AB CD AC BD:
   a=a,b=d on AB; c=k,d=m on KM; a=a,c=k on AK; b=d,d=m on DF. sameSide a.sameSide c BD = a.sameSide k
   DF (step9_ssak). BD-slot distinctPointsOnLine d m DF needs d ≠ m, from d ∈ AB, ¬d ∈ KM (step9_doffkm)
   and m ∈ KM. Parallels AB∥KM (¬KM∩AB flipped), AK∥DF (step9_akdf). refine + euclid_finish. -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step9_ampar (a d k m : Point) (AB KM AK DF : Line)
    (haAB : a.onLine AB) (hdAB : d.onLine AB)
    (hkKM : k.onLine KM) (hmKM : m.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDF : d.onLine DF) (hmDF : m.onLine DF)
    (hdoffKM : ¬(d.onLine KM)) (hssak : a.sameSide k DF)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKDF : ¬(AK.intersectsLine DF)) :
    formParallelogram a d k m AB KM AK DF := by
  euclid_intros
  have hdm : d ≠ m := fun heq => hdoffKM (heq ▸ hmKM)
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  refine ⟨haAB, hdAB, hkKM, hmKM, haAK, hkAK, ⟨hdDF, hmDF, hdm⟩, hssak, hABKM, hAKDF⟩

end Elements.Book2
