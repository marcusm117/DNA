import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15: the gnomon NOP and the square LG together make up the whole square CEFD, which on CD has
   area |c─d|². The figure decomposition (gnomon + LG = △c:e:f + △c:f:d) is step15_decomp (two
   sum_parallelograms_area cuts: KM splits CEFD into the top strip and the bottom strip, then BG splits
   the bottom strip into LHGE and HMFG); the square's area (△c:e:f + △c:f:d = |c─d|²) is step15_sq
   (rectangle_area on CEFD). -/
set_option systemE.solverTime 30 in
theorem helper_2_6_step15 (a b c d e f g h l m : Point) (AB CE DF EF BG KM DE : Line)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF) (hmDF : m.onLine DF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hbBG : b.onLine BG) (hgBG : g.onLine BG) (hhBG : h.onLine BG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hCEDF : ¬(CE.intersectsLine DF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hBGCE : ¬(BG.intersectsLine CE)) (hKMAB : ¬(KM.intersectsLine AB))
    (hdce : ∠ d:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcdf : ∠ c:d:f = ∟) (hdfe : ∠ d:f:e = ∟)
    (hecDF : e.sameSide c DF) :
    (((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
        Triangle.area △ c:e:f + Triangle.area △ c:f:d) ∧
      (Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)|) := by
  euclid_intros
  -- ===== figure preamble (reused off-line / sameSide / parallel / between facts from steps 2/6/7) =====
  have step2_eoff : ¬(e.onLine AB) := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  have step7_boffce : ¬(b.onLine CE) := by sorry
  have step7_coffdf : ¬(c.onLine DF) := by sorry
  have step7_boffdf : ¬(b.onLine DF) := by sorry
  have step7_boffde : ¬(b.onLine DE) := by sorry
  have step7_cnsdBG : ¬(c.sameSide d BG) := by sorry
  have step7_foffab : ¬(f.onLine AB) := by sorry
  have step7_hoffef : ¬(h.onLine EF) := by sorry
  have step7_sscebg : c.sameSide e BG := by sorry
  have step7_eoffbg : ¬(e.onLine BG) := by sorry
  have step7_bgdf : ¬(BG.intersectsLine DF) := by sorry
  have step7_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step7_hoffdf : ¬(h.onLine DF) := by sorry
  have step7_dnseBG : ¬(d.sameSide e BG) := by sorry
  have step7_doffkm : ¬(d.onLine KM) := by sorry
  have step7_foffkm : ¬(f.onLine KM) := by sorry
  have step7_essf : e.sameSide f KM := by sorry
  have step7_dhe : between d h e := by sorry
  have step7_dnse : ¬(d.sameSide e KM) := by sorry
  have step7_dnsf : ¬(d.sameSide f KM) := by sorry
  have step7_dmf : between d m f := by sorry
  have step7_sscl : c.sameSide l BG := by sorry
  have step11_cle : between c l e := by sorry
  -- inline distinctness / sameSide for the square parallelograms
  have hEFneAB : EF ≠ AB := fun heq => step2_eoff (heq ▸ heEF)
  have hCEneDF : CE ≠ DF := fun heq => step7_coffdf (heq ▸ hcCE)
  have hcoffEF : ¬(c.onLine EF) := by
    intro hon; euclid_apply (intersection_lines_common_point c EF AB); euclid_finish
  have hdoffEF : ¬(d.onLine EF) := by
    intro hon; euclid_apply (intersection_lines_common_point d EF AB); euclid_finish
  have hloffDF : ¬(l.onLine DF) := by
    intro hon; euclid_apply (intersection_lines_common_point l DF CE); euclid_finish
  have heoffDF : ¬(e.onLine DF) := by
    intro hon; euclid_apply (intersection_lines_common_point e DF CE); euclid_finish
  have hle : l ≠ e := by euclid_finish
  have hlsse_df : l.sameSide e DF := by
    by_contra hns; euclid_apply (intersection_lines_opposing l e DF CE); euclid_finish
  -- ===== the two square parallelograms, the four cut betweennesses, and the area facts =====
  have step15_sqpar : formParallelogram c d e f AB EF CE DF := by sorry
  have step15_sqpar_a : formParallelogram c e d f CE DF AB EF := by sorry
  have step15_botpar : formParallelogram l m e f KM EF CE DF := by sorry
  have step15_lhm : between l h m := by sorry
  have step15_egf : between e g f := by sorry
  have step15_decomp :
    ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
      Triangle.area △ c:e:f + Triangle.area △ c:f:d := by sorry
  have step15_sq : Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)| := by sorry
  exact ⟨step15_decomp, step15_sq⟩

end Elements.Book2
