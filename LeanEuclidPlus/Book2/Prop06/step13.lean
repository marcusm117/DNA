import SystemE
import Book2.Prop06.step2_eoff
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step7_boffce
import Book2.Prop06.step7_boffde
import Book2.Prop06.step7_coffdf
import Book2.Prop06.step7_boffdf
import Book2.Prop06.step7_cnsdBG
import Book2.Prop06.step7_sscebg
import Book2.Prop06.step7_eoffbg
import Book2.Prop06.step7_bgdf
import Book2.Prop06.step7_ssdb
import Book2.Prop06.step7_hoffef
import Book2.Prop06.step7_hoffdf
import Book2.Prop06.step7_dnseBG
import Book2.Prop06.step7_kmef
import Book2.Prop06.step7_sscl
import Book2.Prop06.step7_cbhl
import Book2.Prop06.step7_dhe
import Book2.Prop06.step7_dnse
import Book2.Prop06.step11_cle
import Book2.Prop06.step11_bdbh
import Book2.Prop06.step13_bhg
import Book2.Prop06.step13_cbh_right
import Book2.Prop06.step13_lhg_right
import Book2.Prop06.step13_par
import Book2.Prop06.step13_rect
import Book2.Prop06.step13_lh_cb
import Book2.Prop06.step13_cl_bh
import Book2.Prop06.step13_le_cb
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.13: LG = |c─b| · |c─b|. The square LG (= rectangle LHGE) has area |l─e|·|l─h| (step13_rect, via
   rectangle_area on the LHGE parallelogram step13_par with the right corner step13_lhg_right), and both
   sides equal CB: |l─h| = |c─b| (step13_lh_cb, CBHL opposite sides) and |l─e| = |c─b| (step13_le_cb,
   length arithmetic using |c─l| = |b─h| = |b─d|). Hence area = |c─b|·|c─b|. -/
theorem helper_2_6_step13 (a b c d e f g h l : Point) (AB CE DF EF BG KM DE : Line)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG) (hhBG : h.onLine BG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hCEDF : ¬(CE.intersectsLine DF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hBGCE : ¬(BG.intersectsLine CE)) (hKMAB : ¬(KM.intersectsLine AB))
    (hdce : ∠ d:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcdf : ∠ c:d:f = ∟) (hdfe : ∠ d:f:e = ∟)
    (hecDF : e.sameSide c DF) :
    Triangle.area △ l:h:g + Triangle.area △ l:g:e = |(c─b)| * |(c─b)| := by
  euclid_intros
  -- ===== figure preamble (reused off-line / sameSide / parallel facts from steps 2/6/7) =====
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffce : ¬(b.onLine CE) := by euclid_apply (helper_2_6_step7_boffce a b c d e AB CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffde : ¬(b.onLine DE) := by euclid_apply (helper_2_6_step7_boffde a b c d e AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_coffdf : ¬(c.onLine DF) := by euclid_apply (helper_2_6_step7_coffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffdf : ¬(b.onLine DF) := by euclid_apply (helper_2_6_step7_boffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_cnsdBG : ¬(c.sameSide d BG) := by euclid_apply (helper_2_6_step7_cnsdBG a b c d AB BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_sscebg : c.sameSide e BG := by euclid_apply (helper_2_6_step7_sscebg b c e CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_eoffbg : ¬(e.onLine BG) := by euclid_apply (helper_2_6_step7_eoffbg b e CE BG (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_bgdf : ¬(BG.intersectsLine DF) := by euclid_apply (helper_2_6_step7_bgdf b c BG CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_ssdb : d.sameSide b KM := by euclid_apply (helper_2_6_step7_ssdb b d h AB KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_hoffef : ¬(h.onLine EF) := by euclid_apply (helper_2_6_step7_hoffef b c d e h AB DE EF CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_hoffdf : ¬(h.onLine DF) := by euclid_apply (helper_2_6_step7_hoffdf b h BG DF (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dnseBG : ¬(d.sameSide e BG) := by euclid_apply (helper_2_6_step7_dnseBG c d e BG (by assumption) (by assumption))
  have step7_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_6_step7_kmef e h AB KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_sscl : c.sameSide l BG := by euclid_apply (helper_2_6_step7_sscl b c l CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_cbhl : formParallelogram c b l h AB KM CE BG := by euclid_apply (helper_2_6_step7_cbhl b c h l AB KM CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dhe : between d h e := by euclid_apply (helper_2_6_step7_dhe b d e h AB DF BG DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dnse : ¬(d.sameSide e KM) := by euclid_apply (helper_2_6_step7_dnse d e h KM (by assumption) (by assumption))
  have step11_cle : between c l e := by euclid_apply (helper_2_6_step11_cle c d e h l AB CE EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step11_bdbh : |(b─d)| = |(b─h)| := by euclid_apply (helper_2_6_step11_bdbh a b c d e h AB CE BG DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- inline distinctness / sameSide for the new sub-nodes
  have hcbd : between c b d := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hbh : b ≠ h := fun heq => step6_hoffab (heq ▸ hbAB)
  have hlc : l ≠ c := by euclid_finish
  have hle : l ≠ e := by euclid_finish
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  have hlsse_bg : l.sameSide e BG := by euclid_finish
  -- ===== the LG corner square =====
  have step13_bhg : between b h g := by euclid_apply (helper_2_6_step13_bhg b d e g h AB EF BG KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hhl : h ≠ l := by euclid_finish
  have hhg : h ≠ g := by euclid_finish
  have step13_cbh_right : ∠ c:b:h = ∟ := by euclid_apply (helper_2_6_step13_cbh_right a b c d e h l AB BG CE KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step13_lhg_right : ∠ l:h:g = ∟ := by euclid_apply (helper_2_6_step13_lhg_right b c g h l AB CE BG KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step13_par : formParallelogram l e h g CE BG KM EF := by euclid_apply (helper_2_6_step13_par e g h l CE BG KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step13_rect : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(l─e)| * |(l─h)| := by euclid_apply (helper_2_6_step13_rect e g h l CE EF KM BG (by assumption) (by assumption))
  have step13_lh_cb : |(l─h)| = |(c─b)| := by euclid_apply (helper_2_6_step13_lh_cb b c h l AB KM CE BG (by assumption))
  have step13_cl_bh : |(c─l)| = |(b─h)| := by euclid_apply (helper_2_6_step13_cl_bh b c h l AB KM CE BG (by assumption))
  have step13_le_cb : |(l─e)| = |(c─b)| := by euclid_apply (helper_2_6_step13_le_cb b c d e l h (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_finish

end Elements.Book2
