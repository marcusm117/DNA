import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.11: AM = |(a─d)| * |(d─b)|. AM is the rectangle ADMK (formParallelogram a d k m, step9_ampar)
   with the right corner ∠ a:k:m = ∟ (step11_akm_right), so rectangle_area gives
   area = |a─d|·|d─m| (step11_rect); and DM = DB (step11_dmdb), so area = |a─d|·|d─b|.
   The AM parallelogram and the DMBH parallelogram / diagonal preamble mirror steps 7 & 9
   (shared sub-nodes). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step11 (a b c d e f g h l m k : Point) (AB CE DF EF BG KM DE AK : Line)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF) (hmDF : m.onLine DF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG) (hhBG : h.onLine BG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (haAK : a.onLine AK) (hkAK : k.onLine AK) (hkKM : k.onLine KM)
    (hCEDF : ¬(CE.intersectsLine DF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hBGCE : ¬(BG.intersectsLine CE)) (hKMAB : ¬(KM.intersectsLine AB))
    (hAKCE : ¬(AK.intersectsLine CE))
    (hdce : ∠ d:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcdf : ∠ c:d:f = ∟) (hdfe : ∠ d:f:e = ∟)
    (hecDF : e.sameSide c DF) :
    Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─b)| := by
  euclid_intros
  -- ===== figure preamble (reused off-line / sameSide / parallel facts from steps 2/6/7/9) =====
  have step2_eoff : ¬(e.onLine AB) := by sorry
  have step6_sska_aoff : ¬(a.onLine CE) := by sorry
  have step7_coffdf : ¬(c.onLine DF) := by sorry
  have step9_aoffdf : ¬(a.onLine DF) := by sorry
  have step7_boffdf : ¬(b.onLine DF) := by sorry
  have step7_boffce : ¬(b.onLine CE) := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  have step7_boffde : ¬(b.onLine DE) := by sorry
  have step7_cnsdBG : ¬(c.sameSide d BG) := by sorry
  have step7_hoffef : ¬(h.onLine EF) := by sorry
  have step7_sscebg : c.sameSide e BG := by sorry
  have step7_eoffbg : ¬(e.onLine BG) := by sorry
  have step9_akdf : ¬(AK.intersectsLine DF) := by sorry
  have step7_bgdf : ¬(BG.intersectsLine DF) := by sorry
  have step7_ssdb : d.sameSide b KM := by sorry
  have step7_doffkm : ¬(d.onLine KM) := by sorry
  have step7_hoffdf : ¬(h.onLine DF) := by sorry
  have step7_dnseBG : ¬(d.sameSide e BG) := by sorry
  have step7_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step9_ssak : a.sameSide k DF := by sorry
  have step9_ampar : formParallelogram a d k m AB KM AK DF := by sorry
  have step7_par1 : formParallelogram d m b h DF BG AB KM := by sorry
  have step7_dhe : between d h e := by sorry
  have step7_dnse : ¬(d.sameSide e KM) := by sorry
  -- inline distinctness for the corner co-interior steps
  have hac : a ≠ c := by euclid_finish
  have hak : a ≠ k := by euclid_finish
  have hkm : k ≠ m := by euclid_finish
  have hABKM : ¬(AB.intersectsLine KM) := by
    intro hx; euclid_apply (intersection_symm AB KM); euclid_finish
  -- ===== the right corner ∠ a:k:m = ∟ =====
  have step11_cle : between c l e := by sorry
  have step11_kac_right : ∠ k:a:c = ∟ := by sorry
  have step11_sscm : c.sameSide m AK := by sorry
  have step11_akm_right : ∠ a:k:m = ∟ := by sorry
  -- ===== rectangle area = |a─d|·|d─m| =====
  have step11_rect : Triangle.area △ a:d:m + Triangle.area △ a:m:k = |(a─d)| * |(d─m)| := by sorry
  -- ===== DM = DB =====
  have step11_dmdb : |(d─m)| = |(d─b)| := by sorry
  rw [step11_rect, step11_dmdb]

end Elements.Book2
