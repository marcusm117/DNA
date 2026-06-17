import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8: CM = AL via AC = CB. Both rectangles with equal bases, so equal areas. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8 (a b c d e f h k l m : Point) (AB KM AK CE BF EF BE : Line)
    (hacb_len : |(a─c)| = |(c─b)|)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hmBF : m.onLine BF) (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (heEF : e.onLine EF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hacd : between a c d) (hcdb : between c d b)
    (hbce : ∠ b:c:e = ∟)
    (hbmf : between b m f) (hbhe : between b h e)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hAKCE : ¬(AK.intersectsLine CE))
    (hEFAB : ¬(EF.intersectsLine AB))
    (hKMEF : ¬(KM.intersectsLine EF))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcmpar : formParallelogram c b l m AB KM CE BF) :
    Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k := by
  euclid_intros
  have step8_alpar : formParallelogram k l a c KM AB AK CE := by
    unfold formParallelogram
    repeat' constructor
    all_goals try (first | assumption | euclid_finish)

  have step8_eoffab : ¬(e.onLine AB) := by sorry
  have step8_boffef : ¬(b.onLine EF) := by sorry
  have step8_hoffab : ¬(h.onLine AB) := by sorry
  have step8_hoffef : ¬(h.onLine EF) := by sorry
  have step8_boffce : ¬(b.onLine CE) := by sorry
  have step8_moffce : ¬(m.onLine CE) := by sorry
  have step8_coffkm : ¬(c.onLine KM) := by sorry
  have step8_eoffkm : ¬(e.onLine KM) := by sorry
  have step8_cle : between c l e := by sorry

  have step8_kal_right : ∠ k:a:c = ∟ := by sorry
  have step8_clm_right : ∠ c:l:m = ∟ := by sorry
  have h1 : Triangle.area △ c:b:m + Triangle.area △ c:m:l = |(c─b)| * |(c─l)| := by
    have h2 := rectangle_area c b l m AB KM CE BF
    have h3 := h2 ⟨hcmpar, step8_clm_right⟩
    euclid_finish
  have h4 : Triangle.area △ a:c:l + Triangle.area △ a:l:k = |(k─a)| * |(k─l)| := by
    have h5 := rectangle_area k l a c KM AB AK CE
    have h5' := h5 ⟨step8_alpar, step8_kal_right⟩
    euclid_finish
  have step8_heights : |(k─a)| = |(c─l)| := by sorry
  have step8_bases : |(k─l)| = |(a─c)| := by sorry
  have h7 : |(k─a)| * |(k─l)| = |(a─c)| * |(c─l)| := by
    rw [step8_heights, step8_bases]
    ring
  rw [h1, h4, h7]
  euclid_finish

end Elements.Book2
