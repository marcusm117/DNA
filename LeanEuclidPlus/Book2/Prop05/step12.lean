import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12: AH = |(a─d)| * |(d─b)|. The rectangle AH = parallelogram ADHK (step11_ahpar) has area
   |a─d|·|d─h| (step12_rect, via rectangle_area + the right corner step12_akh_right), and DH = DB
   (the shared worker step13_dhdb), so AH = |a─d|·|d─b|.
   The parallelogram ADHK and its preamble mirror step11 (shared sub-nodes). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step12 (a b c d e f g h k l : Point) (AB KM AK DG CE EF BF BE : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (haAK : a.onLine AK) (hkAK : k.onLine AK)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (heCE : e.onLine CE) (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hgDG : g.onLine DG)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hacd : between a c d) (hcdb : between c d b) (hdhg : between d h g)
    (hcbf : ∠ c:b:f = ∟) (hbf_len : |(b─f)| = |(c─b)|)
    (hbce : ∠ b:c:e = ∟) (hce_cb : |(c─e)| = |(c─b)|)
    (hKMAB : ¬(KM.intersectsLine AB)) (hAKCE : ¬(AK.intersectsLine CE))
    (hDGCE : ¬(DG.intersectsLine CE)) (hEFAB : ¬(EF.intersectsLine AB)) :
    Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─b)| := by
  euclid_intros
  -- parallelogram ADHK (mirror of step11's preamble; shared sub-nodes)
  have step11_DGneCE : DG ≠ CE := by sorry
  have step11_doffCE : ¬(d.onLine CE) := by sorry
  have step11_eoffDG : ¬(e.onLine DG) := by sorry
  have step11_aoffCE : ¬(a.onLine CE) := by sorry
  have step11_ssak : k.sameSide a CE := by sorry
  have step11_ssdh : d.sameSide h CE := by sorry
  have step11_klh : between k l h := by sorry
  have step11_ahpar : formParallelogram a d k h AB KM AK DG := by sorry
  -- distinctness for the corner co-interior step
  have hac : a ≠ c := by euclid_finish
  have hak : a ≠ k := by euclid_finish
  have hkh : k ≠ h := (between_symm k l h step11_klh).2.2.1
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hint; euclid_apply (intersection_symm AB KM); euclid_finish
  -- AK ∥ DG (the two vertical sides of parallelogram ADHK) and AK ≠ AB
  have hAKDG : ¬(AK.intersectsLine DG) := by euclid_finish
  have hkoffAB : ¬(k.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point k AB KM); euclid_finish
  have hAKAB : AK ≠ AB := fun heq => hkoffAB (heq ▸ hkAK)
  -- off-line + parallel anchors for the between c l e derivation
  have hhoffAB : ¬(h.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point h AB KM); euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point e AB EF); euclid_finish
  have hhoffEF : ¬(h.onLine EF) := by
    intro hon; euclid_apply (intersection_lines_common_point h DG EF); euclid_finish
  have step6_kmef : ¬(KM.intersectsLine EF) := by sorry
  have hce : c ≠ e := by euclid_finish
  have hcoffKM : ¬(c.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point c AB KM); euclid_finish
  have heoffKM : ¬(e.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point e EF KM); euclid_finish
  have hdoffKM : ¬(d.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point d AB KM); euclid_finish
  have hgoffKM : ¬(g.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point g EF KM); euclid_finish
  have hKMCE : KM ≠ CE := fun heq => hcoffKM (by rw [heq]; exact hcCE)
  -- between c l e (l = KM ∩ CE)
  have step12_cle : between c l e := by sorry
  -- corner of rectangle AL at A: ∠ k:a:c = ∟ (shared with step8)
  have step8_kal_right : ∠ k:a:c = ∟ := by sorry
  -- c,h on the same side of AK
  have step12_sshc : c.sameSide h AK := by sorry
  -- right corner ∠ a:k:h = ∟
  have step12_akh_right : ∠ a:k:h = ∟ := by sorry
  -- rectangle area = |a─d|·|d─h|
  have step12_rect : Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─h)| := by sorry
  -- DH = DB (shared worker)
  have step13_dhdb : |(d─h)| = |(d─b)| := by sorry
  rw [step12_rect, step13_dhdb]

end Elements.Book2
