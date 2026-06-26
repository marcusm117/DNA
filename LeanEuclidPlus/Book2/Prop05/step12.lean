import SystemE
import Book2.Prop05.step11_DGneCE
import Book2.Prop05.step11_doffCE
import Book2.Prop05.step11_eoffDG
import Book2.Prop05.step11_aoffCE
import Book2.Prop05.step11_ssak
import Book2.Prop05.step11_ssdh
import Book2.Prop05.step11_klh
import Book2.Prop05.step11_ahpar
import Book2.Prop05.step6_kmef
import Book2.Prop05.step12_cle
import Book2.Prop05.step8_kal_right
import Book2.Prop05.step12_sshc
import Book2.Prop05.step12_akh_right
import Book2.Prop05.step12_rect
import Book2.Prop05.step13_dhdb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12: AH = |(a─d)| * |(d─b)|. The rectangle AH = parallelogram ADHK (step11_ahpar) has area
   |a─d|·|d─h| (step12_rect, via rectangle_area + the right corner step12_akh_right), and DH = DB
   (the shared worker step13_dhdb), so AH = |a─d|·|d─b|.
   The parallelogram ADHK and its preamble mirror step11 (shared sub-nodes). -/
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
  have step11_DGneCE : DG ≠ CE := by euclid_apply (helper_2_5_step11_DGneCE a b c d e f AB CE DG EF BF (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ∠ c:b:f = ∟; assumption)) (by euclid_assumption "" (show |(b─f)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have step11_doffCE : ¬(d.onLine CE) := by euclid_apply (helper_2_5_step11_doffCE d DG CE (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show DG ≠ CE; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step11_eoffDG : ¬(e.onLine DG) := by euclid_apply (helper_2_5_step11_eoffDG e DG CE (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show DG ≠ CE; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step11_aoffCE : ¬(a.onLine CE) := by euclid_apply (helper_2_5_step11_aoffCE a c d AB CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)))
  have step11_ssak : k.sameSide a CE := by euclid_apply (helper_2_5_step11_ssak a k AK CE (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show ¬(a.onLine CE); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)))
  have step11_ssdh : d.sameSide h CE := by euclid_apply (helper_2_5_step11_ssdh d h DG CE (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step11_klh : between k l h := by euclid_apply (helper_2_5_step11_klh a c d h k l AB KM CE AK DG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show k.sameSide a CE; assumption)) (by euclid_assumption "" (show d.sameSide h CE; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step11_ahpar : formParallelogram a d k h AB KM AK DG := by euclid_apply (helper_2_5_step11_ahpar a d e h k l AB KM AK DG CE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show ¬(a.onLine CE); assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show ¬(e.onLine DG); assumption)) (by euclid_assumption "" (show between k l h; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
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
  have step6_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_5_step6_kmef e h AB KM EF (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(e.onLine AB); assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
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
  have step12_cle : between c l e := by euclid_apply (helper_2_5_step12_cle c d e g h l AB EF KM CE DG (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show between d h g; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show ¬(c.onLine KM); assumption)) (by euclid_assumption "" (show ¬(e.onLine KM); assumption)) (by euclid_assumption "" (show ¬(d.onLine KM); assumption)) (by euclid_assumption "" (show ¬(g.onLine KM); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)) (by euclid_assumption "" (show KM ≠ CE; assumption)))
  -- corner of rectangle AL at A: ∠ k:a:c = ∟ (shared with step8)
  have step8_kal_right : ∠ k:a:c = ∟ := by euclid_apply (helper_2_5_step8_kal_right a b c d e k l AB AK CE KM EF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show between c l e; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  -- c,h on the same side of AK
  have step12_sshc : c.sameSide h AK := by euclid_apply (helper_2_5_step12_sshc a c d h k AB AK DG (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show AK ≠ AB; assumption)) (by euclid_assumption "" (show ¬(AK.intersectsLine DG); assumption)))
  -- right corner ∠ a:k:h = ∟
  have step12_akh_right : ∠ a:k:h = ∟ := by euclid_apply (helper_2_5_step12_akh_right a c h k AB AK KM (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine AK; assumption)) (by euclid_assumption "" (show k.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ k; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show ∠ k:a:c = ∟; assumption)) (by euclid_assumption "" (show c.sameSide h AK; assumption)) (by euclid_assumption "" (show ¬(AB.intersectsLine KM); assumption)))
  -- rectangle area = |a─d|·|d─h|
  have step12_rect : Triangle.area △ a:d:h + Triangle.area △ a:h:k = |(a─d)| * |(d─h)| := by euclid_apply (helper_2_5_step12_rect a d h k AB KM AK DG (by euclid_assumption "" (show formParallelogram a d k h AB KM AK DG; assumption)) (by euclid_assumption "" (show ∠ a:k:h = ∟; assumption)))
  -- DH = DB (shared worker)
  have step13_dhdb : |(d─h)| = |(d─b)| := by euclid_apply (helper_2_5_step13_dhdb b c d e h AB CE DG BE (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  rw [step12_rect, step13_dhdb]

end Elements.Book2
