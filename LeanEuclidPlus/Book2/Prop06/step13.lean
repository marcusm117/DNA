import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.13: LG = |c─b| · |c─b|. The square LG (= rectangle LHGE) has area |l─e|·|l─h| (step13_rect, via
   rectangle_area on the LHGE parallelogram step13_par with the right corner step13_lhg_right), and both
   sides equal CB: |l─h| = |c─b| (step13_lh_cb, CBHL opposite sides) and |l─e| = |c─b| (step13_le_cb,
   length arithmetic using |c─l| = |b─h| = |b─d|). Hence area = |c─b|·|c─b|. -/
set_option systemE.solverTime 30 in
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
  have step2_eoff : ¬(e.onLine AB) := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  have step7_boffce : ¬(b.onLine CE) := by sorry
  have step7_boffde : ¬(b.onLine DE) := by sorry
  have step7_coffdf : ¬(c.onLine DF) := by sorry
  have step7_boffdf : ¬(b.onLine DF) := by sorry
  have step7_cnsdBG : ¬(c.sameSide d BG) := by sorry
  have step7_sscebg : c.sameSide e BG := by sorry
  have step7_eoffbg : ¬(e.onLine BG) := by sorry
  have step7_bgdf : ¬(BG.intersectsLine DF) := by sorry
  have step7_ssdb : d.sameSide b KM := by sorry
  have step7_hoffef : ¬(h.onLine EF) := by sorry
  have step7_hoffdf : ¬(h.onLine DF) := by sorry
  have step7_dnseBG : ¬(d.sameSide e BG) := by sorry
  have step7_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step7_sscl : c.sameSide l BG := by sorry
  have step7_cbhl : formParallelogram c b l h AB KM CE BG := by sorry
  have step7_dhe : between d h e := by sorry
  have step7_dnse : ¬(d.sameSide e KM) := by sorry
  have step11_cle : between c l e := by sorry
  have step11_bdbh : |(b─d)| = |(b─h)| := by sorry
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
  have step13_bhg : between b h g := by sorry
  have hhl : h ≠ l := by euclid_finish
  have hhg : h ≠ g := by euclid_finish
  have step13_cbh_right : ∠ c:b:h = ∟ := by sorry
  have step13_lhg_right : ∠ l:h:g = ∟ := by sorry
  have step13_par : formParallelogram l e h g CE BG KM EF := by sorry
  have step13_rect : Triangle.area △ l:e:g + Triangle.area △ l:g:h = |(l─e)| * |(l─h)| := by sorry
  have step13_lh_cb : |(l─h)| = |(c─b)| := by sorry
  have step13_cl_bh : |(c─l)| = |(b─h)| := by sorry
  have step13_le_cb : |(l─e)| = |(c─b)| := by sorry
  euclid_finish

end Elements.Book2
