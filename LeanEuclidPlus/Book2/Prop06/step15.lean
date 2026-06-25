import SystemE
import Book2.Prop06.step2_eoff
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step7_boffce
import Book2.Prop06.step7_coffdf
import Book2.Prop06.step7_boffdf
import Book2.Prop06.step7_boffde
import Book2.Prop06.step7_cnsdBG
import Book2.Prop06.step7_foffab
import Book2.Prop06.step7_hoffef
import Book2.Prop06.step7_sscebg
import Book2.Prop06.step7_eoffbg
import Book2.Prop06.step7_bgdf
import Book2.Prop06.step7_kmef
import Book2.Prop06.step7_hoffdf
import Book2.Prop06.step7_dnseBG
import Book2.Prop06.step7_doffkm
import Book2.Prop06.step7_foffkm
import Book2.Prop06.step7_essf
import Book2.Prop06.step7_dhe
import Book2.Prop06.step7_dnse
import Book2.Prop06.step7_dnsf
import Book2.Prop06.step7_dmf
import Book2.Prop06.step7_sscl
import Book2.Prop06.step11_cle
import Book2.Prop06.step15_sqpar
import Book2.Prop06.step15_sqpar_a
import Book2.Prop06.step15_botpar
import Book2.Prop06.step15_lhm
import Book2.Prop06.step15_egf
import Book2.Prop06.step15_decomp
import Book2.Prop06.step15_sq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15: the gnomon NOP and the square LG together make up the whole square CEFD, which on CD has
   area |c─d|². The figure decomposition (gnomon + LG = △c:e:f + △c:f:d) is step15_decomp (two
   sum_parallelograms_area cuts: KM splits CEFD into the top strip and the bottom strip, then BG splits
   the bottom strip into LHGE and HMFG); the square's area (△c:e:f + △c:f:d = |c─d|²) is step15_sq
   (rectangle_area on CEFD). -/
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
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffce : ¬(b.onLine CE) := by euclid_apply (helper_2_6_step7_boffce a b c d e AB CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_coffdf : ¬(c.onLine DF) := by euclid_apply (helper_2_6_step7_coffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffdf : ¬(b.onLine DF) := by euclid_apply (helper_2_6_step7_boffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_boffde : ¬(b.onLine DE) := by euclid_apply (helper_2_6_step7_boffde a b c d e AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_cnsdBG : ¬(c.sameSide d BG) := by euclid_apply (helper_2_6_step7_cnsdBG a b c d AB BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_foffab : ¬(f.onLine AB) := by euclid_apply (helper_2_6_step7_foffab a b c d f AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_hoffef : ¬(h.onLine EF) := by euclid_apply (helper_2_6_step7_hoffef b c d e h AB DE EF CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_sscebg : c.sameSide e BG := by euclid_apply (helper_2_6_step7_sscebg b c e CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_eoffbg : ¬(e.onLine BG) := by euclid_apply (helper_2_6_step7_eoffbg b e CE BG (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_bgdf : ¬(BG.intersectsLine DF) := by euclid_apply (helper_2_6_step7_bgdf b c BG CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_6_step7_kmef e h AB KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_hoffdf : ¬(h.onLine DF) := by euclid_apply (helper_2_6_step7_hoffdf b h BG DF (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dnseBG : ¬(d.sameSide e BG) := by euclid_apply (helper_2_6_step7_dnseBG c d e BG (by assumption) (by assumption))
  have step7_doffkm : ¬(d.onLine KM) := by euclid_apply (helper_2_6_step7_doffkm d h AB KM (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_foffkm : ¬(f.onLine KM) := by euclid_apply (helper_2_6_step7_foffkm f h EF KM (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_essf : e.sameSide f KM := by euclid_apply (helper_2_6_step7_essf e f h EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dhe : between d h e := by euclid_apply (helper_2_6_step7_dhe b d e h AB DF BG DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_dnse : ¬(d.sameSide e KM) := by euclid_apply (helper_2_6_step7_dnse d e h KM (by assumption) (by assumption))
  have step7_dnsf : ¬(d.sameSide f KM) := by euclid_apply (helper_2_6_step7_dnsf d e f KM (by assumption) (by assumption))
  have step7_dmf : between d m f := by euclid_apply (helper_2_6_step7_dmf d f h m AB KM DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step7_sscl : c.sameSide l BG := by euclid_apply (helper_2_6_step7_sscl b c l CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step11_cle : between c l e := by euclid_apply (helper_2_6_step11_cle c d e h l AB CE EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
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
  have step15_sqpar : formParallelogram c d e f AB EF CE DF := by euclid_apply (helper_2_6_step15_sqpar c d e f AB EF CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_sqpar_a : formParallelogram c e d f CE DF AB EF := by euclid_apply (helper_2_6_step15_sqpar_a c d e f AB EF CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_botpar : formParallelogram l m e f KM EF CE DF := by euclid_apply (helper_2_6_step15_botpar e f l m KM EF CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_lhm : between l h m := by euclid_apply (helper_2_6_step15_lhm b c d h l m CE DF BG KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_egf : between e g f := by euclid_apply (helper_2_6_step15_egf b c d e f g CE DF BG EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_decomp :
    ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
      Triangle.area △ c:e:f + Triangle.area △ c:f:d := by euclid_apply (helper_2_6_step15_decomp c d e f g h l m AB CE DF EF KM BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step15_sq : Triangle.area △ c:e:f + Triangle.area △ c:f:d = |(c─d)| * |(c─d)| := by euclid_apply (helper_2_6_step15_sq c d e f AB EF CE DF (by assumption) (by assumption) (by assumption))
  exact ⟨step15_decomp, step15_sq⟩

end Elements.Book2
