import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11: AH = gnomon NOP = DF + CH. AH (= par ADHK) is cut by CE (at c on AB, l on KM) into
   AL (ACLK) and CH (CDHL). sum_parallelograms_area on par ADHK with between a c d and between k l h
   gives the area split; then substitute step9 (AL = DF). Sub-nodes: step11_klh (between k l h),
   step11_ahpar (formParallelogram a d h k AB KM AK DG). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step11 (a b c d e f g h k l : Point) (AB KM AK DG CE EF BF : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (heCE : e.onLine CE) (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hacd : between a c d) (hcdb : between c d b) (hdhg : between d h g)
    (hcbf : ∠ c:b:f = ∟) (hbf_len : |(b─f)| = |(c─b)|)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) (hEFAB : ¬(EF.intersectsLine AB))
    (hstep9 : Triangle.area △ a:c:l + Triangle.area △ a:l:k =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g) :
    Triangle.area △ a:d:h + Triangle.area △ a:h:k =
      (Triangle.area △ d:b:f + Triangle.area △ d:f:g) +
      (Triangle.area △ c:d:h + Triangle.area △ c:h:l) := by
  euclid_intros
  -- DG ≠ CE: SMT can derive from rich Main context (angles, lengths, betweenness, parallels)
  have step11_DGneCE : DG ≠ CE := by sorry
  -- derive ¬d.onLine CE using DG ≠ CE anchor + d ∈ DG + DG ∥ CE
  have step11_doffCE : ¬(d.onLine CE) := by sorry
  -- derive ¬e.onLine DG using DG ≠ CE anchor + e ∈ CE + DG ∥ CE
  have step11_eoffDG : ¬(e.onLine DG) := by sorry
  -- ¬a.onLine CE: if a ∈ CE, then a,c ∈ AB ∩ CE (a≠c from between a c d) → AB=CE → d ∈ CE
  --   contradicts step11_doffCE
  have step11_aoffCE : ¬(a.onLine CE) := by sorry
  -- sameSide facts needed for step11_klh betweenness (k,a on AK-side of CE; d,h on DG-side of CE)
  have step11_ssak : k.sameSide a CE := by sorry
  have step11_ssdh : d.sameSide h CE := by sorry
  have step11_klh : between k l h := by sorry
  -- correct order: a,d on AB; k,h on KM; a,k on AK (left); d,h on DG (right)
  have step11_ahpar : formParallelogram a d k h AB KM AK DG := by sorry
  euclid_apply (sum_parallelograms_area a d k h c l AB KM AK DG)
  rw [← hstep9]
  euclid_finish

end Elements.Book2
