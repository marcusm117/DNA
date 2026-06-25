import SystemE
import Book2.Prop05.step6_kmef
import Book2.Prop05.step15_cle
import Book2.Prop05.step6_cdhl
import Book2.Prop05.step15_ss_eh
import Book2.Prop05.step15_ssce
import Book2.Prop05.step15_cdh_right
import Book2.Prop05.step15_par
import Book2.Prop05.step15_lhg_right
import Book2.Prop05.step15_rect
import Book2.Prop05.step15_lh_cd
import Book2.Prop05.step15_cl_dh
import Book2.Prop05.step13_dhdb
import Book2.Prop05.step15_le_cd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15: LG = |CD|². The square LG (= rectangle LEGH) has area |l─e|·|l─h| (step15_rect, via
   rectangle_area on the LEGH parallelogram step15_par with the right corner step15_lhg_right), and
   both sides equal CD: |l─h| = |c─d| (step15_lh_cd, CDHL opposite sides) and |l─e| = |c─d|
   (step15_le_cd, length arithmetic using |c─l| = |d─h| = |d─b|). Hence area = |c─d|·|c─d|. -/
theorem helper_2_5_step15 (b c d e g h l : Point) (AB CE DG KM EF BE : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hlCE : l.onLine CE) (heCE : e.onLine CE) (hcCE : c.onLine CE)
    (hgDG : g.onLine DG) (hhDG : h.onLine DG) (hdDG : d.onLine DG)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hbBE : b.onLine BE) (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hbe : b ≠ e)
    (hcdb : between c d b) (hdhg : between d h g)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hKMAB : ¬(KM.intersectsLine AB)) (hDGCE : ¬(DG.intersectsLine CE))
    (hEFAB : ¬(EF.intersectsLine AB)) :
    Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(c─d)| * |(c─d)| := by
  euclid_intros
  -- parallel + distinctness anchors
  have hCEDG : ¬(CE.intersectsLine DG) := by
    intro hint; euclid_apply (intersection_symm CE DG); euclid_finish
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hint; euclid_apply (intersection_symm AB KM); euclid_finish
  have hle : l ≠ e := by euclid_finish
  have hdc : d ≠ c := by euclid_finish
  have hdh : d ≠ h := by euclid_finish
  have hhg : h ≠ g := by euclid_finish
  have hhl : h ≠ l := by euclid_finish
  -- off-line anchors
  have hhoffAB : ¬(h.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point h AB KM); euclid_finish
  have heoffAB : ¬(e.onLine AB) := by
    intro hon; euclid_apply (intersection_lines_common_point e AB EF); euclid_finish
  have hhoffEF : ¬(h.onLine EF) := by
    intro hon; euclid_apply (intersection_lines_common_point h DG EF); euclid_finish
  -- KM ∥ EF (shared sub-node from step6)
  have step6_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_5_step6_kmef e h AB KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- off-line anchors needed by step15_cle (derive before the node)
  have hcoffKM : ¬(c.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point c KM AB); euclid_finish
  have heoffKM : ¬(e.onLine KM) := by
    intro hon; euclid_apply (intersection_lines_common_point e KM EF); euclid_finish
  have hloffDG : ¬(l.onLine DG) := by
    intro hcon; euclid_apply (intersection_lines_common_point l DG CE); euclid_finish
  -- between c l e: l = KM∩CE, c on AB (below KM), e on EF (above KM)
  have step15_cle : between c l e := by euclid_apply (helper_2_5_step15_cle c d e g h l AB CE DG EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- c.sameSide l DG: both c,l on CE ∥ DG
  have hcoffDG : ¬(c.onLine DG) := by
    intro hon; euclid_apply (intersection_lines_common_point c DG CE); euclid_finish
  have hcsslDG : c.sameSide l DG := by
    by_contra hns
    euclid_apply (intersection_lines_opposing c l DG CE)
    euclid_finish
  -- CDHL parallelogram (shared sub-node from step6)
  have step6_cdhl : formParallelogram c d l h AB KM CE DG := by euclid_apply (helper_2_5_step6_cdhl c d h l AB KM CE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hlc : l ≠ c := by euclid_finish
  -- e.sameSide h AB: via between b h e (b on AB, KM between AB and EF on line BE)
  have heoffAB' : ¬(e.onLine AB) := heoffAB
  -- @args: b d e g h AB BE EF KM
  have step15_ss_eh : e.sameSide h AB := by euclid_apply (helper_2_5_step15_ss_eh b d e g h AB BE EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- sameSide: l.sameSide e DG (CE ∥ DG, both on CE)
  -- @args: d l e CE DG
  have step15_ssce : l.sameSide e DG := by euclid_apply (helper_2_5_step15_ssce d l e CE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- right angle ∠ c:d:h = ∟ (CD ⊥ DG, DG ∥ CE ⊥ AB)
  have step15_cdh_right : ∠ c:d:h = ∟ := by euclid_apply (helper_2_5_step15_cdh_right b c d e h AB CE DG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- the LEGH square (parallelogram) and its right corner at H
  have step15_par : formParallelogram l e h g CE DG KM EF := by euclid_apply (helper_2_5_step15_par e g h l CE DG KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_lhg_right : ∠ l:h:g = ∟ := by euclid_apply (helper_2_5_step15_lhg_right c d g h l AB CE DG KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- rectangle area = |l─e|·|l─h|
  have step15_rect : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(l─e)| * |(l─h)| := by euclid_apply (helper_2_5_step15_rect e g h l CE EF KM DG (by assumption) (by assumption))
  -- both sides equal CD
  have step15_lh_cd : |(l─h)| = |(c─d)| := by euclid_apply (helper_2_5_step15_lh_cd c d h l AB KM CE DG (by assumption))
  -- |c─l| = |d─h| (CDHL opposite sides) and |d─h| = |d─b| (shared step13)
  have step15_cl_dh : |(c─l)| = |(d─h)| := by euclid_apply (helper_2_5_step15_cl_dh c d h l AB KM CE DG (by assumption))
  have step13_dhdb : |(d─h)| = |(d─b)| := by euclid_apply (helper_2_5_step13_dhdb b c d e h AB CE DG BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_le_cd : |(l─e)| = |(c─d)| := by euclid_apply (helper_2_5_step15_le_cd b c d e l h (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  rw [step15_rect, step15_le_cd, step15_lh_cd]

end Elements.Book2
