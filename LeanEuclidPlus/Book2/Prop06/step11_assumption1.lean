import SystemE
import Book1.Prop06.Main
import Book1Variants.Prop34
import Book2.Prop06.step2_eoff
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step7_boffce
import Book2.Prop06.step7_coffdf
import Book2.Prop06.step7_boffdf
import Book2.Prop06.step7_cnsdBG
import Book2.Prop06.step7_sscebg
import Book2.Prop06.step7_eoffbg
import Book2.Prop06.step7_dnseBG
import Book2.Prop06.step7_bgdf
import Book2.Prop06.step7_hoffdf
import Book2.Prop06.step7_ssdb
import Book2.Prop06.step7_par1
import Book2.Prop06.step7_boffde
import Book2.Prop06.step7_dhe
import Book2.Prop06.step11_dmdb_iso
import Book2.Prop06.step11_dmdb_corr
import Book2.Prop06.step11_dmdb_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.11 @assumption: |(d─m)| = |(d─b)| ("DM is equal to DB").
   Derives all internal figure facts from Main-suppliable hyps, then reuses the shared sub-nodes
   step11_dmdb_iso / _corr / _tri. Chain:
   - step2_eoff (e ∉ AB), step6_hoffab (h ∉ AB), step7_boffce/coffdf/boffdf (off-line),
   - step7_cnsdBG, step7_sscebg, step7_dnseBG, step7_eoffbg,
   - step7_bgdf (BG ∦ DF), step7_hoffdf (h ∉ DF), step7_ssdb (d,b same side KM),
   - step7_par1 (formParallelogram d m b h DF BG AB KM),
   - step7_boffde (b ∉ DE), step7_dhe (between d h e),
   - then the DM=DB proof via iso/corr/tri. -/
theorem helper_2_6_step11_assumption1 (a b c d e f h m : Point) (AB CE DF BG KM DE : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF) (hmDF : m.onLine DF)
    (hbBG : b.onLine BG) (hhBG : h.onLine BG)
    (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hacb : between a c b) (habd : between a b d)
    (hce : |(c─e)| = |(c─d)|) (hdce : ∠ d:c:e = ∟)
    (hdf : |(d─f)| = |(c─d)|) (hcdf : ∠ c:d:f = ∟)
    (hCEDF : ¬(CE.intersectsLine DF))
    (hBGCE : ¬(BG.intersectsLine CE))
    (hKMAB : ¬(KM.intersectsLine AB)) :
    |(d─m)| = |(d─b)| := by
  euclid_intros
  -- derive e ∉ AB
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  -- derive h ∉ AB
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  -- derive b ∉ CE
  have step7_boffce : ¬(b.onLine CE) := by euclid_apply (helper_2_6_step7_boffce a b c d e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  -- derive c ∉ DF
  have step7_coffdf : ¬(c.onLine DF) := by euclid_apply (helper_2_6_step7_coffdf a b c d f AB DF (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)))
  -- derive b ∉ DF
  have step7_boffdf : ¬(b.onLine DF) := by euclid_apply (helper_2_6_step7_boffdf a b c d f AB DF (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show f.onLine DF; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(d─f)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ c:d:f = ∟; assumption)))
  -- derive ¬c.sameSide d BG
  have step7_cnsdBG : ¬(c.sameSide d BG) := by euclid_apply (helper_2_6_step7_cnsdBG a b c d AB BG (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)))
  -- derive c.sameSide e BG
  have step7_sscebg : c.sameSide e BG := by euclid_apply (helper_2_6_step7_sscebg b c e CE BG (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show ¬(b.onLine CE); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  -- derive ¬e.onLine BG
  have step7_eoffbg : ¬(e.onLine BG) := by euclid_apply (helper_2_6_step7_eoffbg b e CE BG (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show ¬(b.onLine CE); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  -- derive ¬d.sameSide e BG
  have step7_dnseBG : ¬(d.sameSide e BG) := by euclid_apply (helper_2_6_step7_dnseBG c d e BG (by euclid_assumption "" (show ¬(c.sameSide d BG); assumption)) (by euclid_assumption "" (show c.sameSide e BG; assumption)))
  -- derive BG ∦ DF
  have step7_bgdf : ¬(BG.intersectsLine DF) := by euclid_apply (helper_2_6_step7_bgdf b c BG CE DF (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬(b.onLine CE); assumption)) (by euclid_assumption "" (show ¬(c.onLine DF); assumption)) (by euclid_assumption "" (show ¬(b.onLine DF); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine DF); assumption)))
  -- derive h ∉ DF
  have step7_hoffdf : ¬(h.onLine DF) := by euclid_apply (helper_2_6_step7_hoffdf b h BG DF (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show ¬(b.onLine DF); assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine DF); assumption)))
  -- derive d.sameSide b KM
  have step7_ssdb : d.sameSide b KM := by euclid_apply (helper_2_6_step7_ssdb b d h AB KM (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  -- derive formParallelogram d m b h DF BG AB KM
  have step7_par1 : formParallelogram d m b h DF BG AB KM := by euclid_apply (helper_2_6_step7_par1 b d h m DF BG AB KM (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show m.onLine DF; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine DF); assumption)) (by euclid_assumption "" (show d.sameSide b KM; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine DF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  -- derive b ∉ DE
  have step7_boffde : ¬(b.onLine DE) := by euclid_apply (helper_2_6_step7_boffde a b c d e AB DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a b d; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)))
  -- derive between d h e
  have step7_dhe : between d h e := by euclid_apply (helper_2_6_step7_dhe b d e h AB DF BG DE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DF; assumption)) (by euclid_assumption "" (show ¬(b.onLine DE); assumption)) (by euclid_assumption "" (show ¬(e.onLine AB); assumption)) (by euclid_assumption "" (show ¬(h.onLine DF); assumption)) (by euclid_assumption "" (show ¬(e.onLine BG); assumption)) (by euclid_assumption "" (show ¬(d.sameSide e BG); assumption)))
  -- derive the needed sameSide and distinctness for the diagonal-angle chain
  have hbd : b ≠ d := by euclid_finish
  have hcbd : between c b d := by euclid_finish
  have hcoffDE : ¬(c.onLine DE) := by
    intro hon; euclid_apply (intersection_lines_common_point c DE AB); euclid_finish
  have hbcDE : b.sameSide c DE := by
    by_contra hns; euclid_apply (intersection_lines_opposing b c DE AB); euclid_finish
  have hcd : c ≠ d := by euclid_finish
  have hcene : c ≠ e := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  -- sub-nodes for the diagonal-angle chain
  have step11_dmdb_iso : ∠ c:d:e = ∠ c:e:d := by euclid_apply (helper_2_6_step11_dmdb_iso c d e AB DE CE (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─d)|; assumption)) (by euclid_assumption "" (show ∠ d:c:e = ∟; assumption)) (by euclid_assumption "" (show c ≠ d; assumption)) (by euclid_assumption "" (show c ≠ e; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show ¬(c.onLine DE); assumption)))
  have step11_dmdb_corr : ∠ d:h:b = ∠ c:e:d := by euclid_apply (helper_2_6_step11_dmdb_corr b c d e h BG CE DE (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show between d h e; assumption)) (by euclid_assumption "" (show b.sameSide c DE; assumption)) (by euclid_assumption "" (show ¬(BG.intersectsLine CE); assumption)))
  have step11_dmdb_tri : formTriangle b d h AB DE BG := by euclid_apply (helper_2_6_step11_dmdb_tri b d h AB DE BG (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine BG; assumption)) (by euclid_assumption "" (show ¬(b.onLine DE); assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show b ≠ d; assumption)))
  -- ray at d: ∠ c:d:e = ∠ b:d:h
  have hray2 : ∠ c:d:e = ∠ b:d:h := by
    euclid_apply (equal_angles d c b e h AB DE)
    euclid_finish
  -- base angles equal
  have hbase : (∠ b:d:h : ℝ) = ∠ b:h:d := by euclid_finish
  -- right-isosceles ⟹ |b─d| = |b─h| [Prop.~1.6]
  have hbdbh : |(b─d)| = |(b─h)| := by
    euclid_apply (proposition_6 b d h AB DE BG)
    euclid_finish
  -- opposite sides of parallelogram DMBH ⟹ |d─m| = |b─h| [Prop.~1.34]
  have hdmbh : |(d─m)| = |(b─h)| := by
    euclid_apply (proposition_34' d m b h DF BG AB KM)
    euclid_finish
  euclid_finish

end Elements.Book2
