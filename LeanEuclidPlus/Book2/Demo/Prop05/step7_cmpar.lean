import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7 sub: formParallelogram c b l m AB KM CE BF (rectangle CM).
   def p1 p2 p3 p4 L1 L2 L3 L4: p1=c,p2=b on L1=AB; p3=l,p4=m on L2=KM;
   p1=c,p3=l on L3=CE; p2=b,p4=m on L4=BF; p1.sameSide p3 L4 = c.sameSide l BF;
   ¬(AB∥KM), ¬(CE∥BF).
   b ≠ m: b on AB, m not on AB (KM ∥ AB and m on KM but not AB). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7_cmpar (b c l m : Point) (AB KM CE BF : Line)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hbBF : b.onLine BF) (hmBF : m.onLine BF)
    (hboffKM : ¬(b.onLine KM))
    (hcsslBF : c.sameSide l BF)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF)) :
    formParallelogram c b l m AB KM CE BF := by
  euclid_intros
  have hbm : b ≠ m := by euclid_finish
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  have hCEBF' : ¬(CE.intersectsLine BF) := hCEBF
  exact ⟨hcAB, hbAB, hlKM, hmKM, hcCE, hlCE, ⟨hbBF, hmBF, hbm⟩, hcsslBF, hABKM, hCEBF'⟩

end Elements.Book2
