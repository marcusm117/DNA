import SystemE
import Book2.Prop06.step2_eoff
import Book2.Prop06.step7_foffab
import Book2.Prop06.step6_hoffab
import Book2.Prop06.step7_boffce
import Book2.Prop06.step7_coffdf
import Book2.Prop06.step7_boffdf
import Book2.Prop06.step7_hoffef
import Book2.Prop06.step7_efne
import Book2.Prop06.step7_kmef
import Book2.Prop06.step7_bgdf
import Book2.Prop06.step7_hoffdf
import Book2.Prop06.step7_eoffbg
import Book2.Prop06.step7_foffkm
import Book2.Prop06.step7_doffkm
import Book2.Prop06.step7_big
import Book2.Prop06.step7_boffde
import Book2.Prop06.step7_sscebg
import Book2.Prop06.step7_cnsdBG
import Book2.Prop06.step7_dnseBG
import Book2.Prop06.step7_dhe
import Book2.Prop06.step7_dnse
import Book2.Prop06.step7_essf
import Book2.Prop06.step7_dnsf
import Book2.Prop06.step7_dmf
import Book2.Prop06.step7_ssdb
import Book2.Prop06.step7_sshl
import Book2.Prop06.step7_sscl
import Book2.Prop06.step7_sshg
import Book2.Prop06.step7_par1
import Book2.Prop06.step7_par2
import Book2.Prop06.step7_cbhl
import Book2.Prop06.step7_hmfg
import Book2.Prop06.step7_compl
import Book2.Prop06.step7_lhs
import Book2.Prop06.step7_rhs
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7: the complements CBHL and HMFG of the square CEFD about diagonal DE are equal [Prop.~1.43].
   proposition_43 on CEFD (diagonal D-E through h), with the two parallelograms ABOUT the diagonal
   (DMBH at corner D = `d m b h`, HGLE at corner E = `h g l e`), yields
   △b:c:l + △b:l:h = △m:h:g + △m:g:f. The parallelogram_area bridges (step7_lhs on CBHL, step7_rhs on
   HMFG) recast those to the goal's triangulation △c:b:h + △c:h:l = △h:m:f + △h:f:g. -/
theorem helper_2_6_step7 (a b c d e f g h l m : Point) (AB DE CE DF EF BG KM : Line)
    (hacb : between a c b) (habd : between a b d) (hce : |(c─e)| = |(c─d)|) (hdf : |(d─f)| = |(c─d)|)
    (haAB : a.onLine AB)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
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
    Triangle.area △ c:b:h + Triangle.area △ c:h:l = Triangle.area △ h:m:f + Triangle.area △ h:f:g := by
  euclid_intros
  -- shared off-line anchors
  have step2_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_6_step2_eoff a b c d e AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_foffab : ¬(f.onLine AB) := by euclid_apply (helper_2_6_step7_foffab a b c d f AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step6_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_6_step6_hoffab a b c d e h AB CE DE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_boffce : ¬(b.onLine CE) := by euclid_apply (helper_2_6_step7_boffce a b c d e AB CE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_coffdf : ¬(c.onLine DF) := by euclid_apply (helper_2_6_step7_coffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_boffdf : ¬(b.onLine DF) := by euclid_apply (helper_2_6_step7_boffdf a b c d f AB DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_hoffef : ¬(h.onLine EF) := by euclid_apply (helper_2_6_step7_hoffef b c d e h AB DE EF CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- shared line-distinctness + parallels
  have step7_efne : EF ≠ AB := by euclid_apply (helper_2_6_step7_efne a b c d e AB CE EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_6_step7_kmef e h AB KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_bgdf : ¬(BG.intersectsLine DF) := by euclid_apply (helper_2_6_step7_bgdf b c BG CE DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- derived off-line facts (need the parallels above)
  have step7_hoffdf : ¬(h.onLine DF) := by euclid_apply (helper_2_6_step7_hoffdf b h BG DF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_eoffbg : ¬(e.onLine BG) := by euclid_apply (helper_2_6_step7_eoffbg b e CE BG (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_foffkm : ¬(f.onLine KM) := by euclid_apply (helper_2_6_step7_foffkm f h EF KM (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_doffkm : ¬(d.onLine KM) := by euclid_apply (helper_2_6_step7_doffkm d h AB KM (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the square
  have step7_big : formParallelogram d f c e DF CE AB EF := by euclid_apply (helper_2_6_step7_big a b c d e f AB DF CE EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- foot betweenness between d m f (cone: opposite-sides of d,f across KM)
  have step7_boffde : ¬(b.onLine DE) := by euclid_apply (helper_2_6_step7_boffde a b c d e AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_sscebg : c.sameSide e BG := by euclid_apply (helper_2_6_step7_sscebg b c e CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_cnsdBG : ¬(c.sameSide d BG) := by euclid_apply (helper_2_6_step7_cnsdBG a b c d AB BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dnseBG : ¬(d.sameSide e BG) := by euclid_apply (helper_2_6_step7_dnseBG c d e BG (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dhe : between d h e := by euclid_apply (helper_2_6_step7_dhe b d e h AB DF BG DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dnse : ¬(d.sameSide e KM) := by euclid_apply (helper_2_6_step7_dnse d e h KM (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_essf : e.sameSide f KM := by euclid_apply (helper_2_6_step7_essf e f h EF KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dnsf : ¬(d.sameSide f KM) := by euclid_apply (helper_2_6_step7_dnsf d e f KM (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_dmf : between d m f := by euclid_apply (helper_2_6_step7_dmf d f h m AB KM DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the four sameSides (Family-3, two points on a parallel)
  have step7_ssdb : d.sameSide b KM := by euclid_apply (helper_2_6_step7_ssdb b d h AB KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_sshl : h.sameSide l EF := by euclid_apply (helper_2_6_step7_sshl h l KM EF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_sscl : c.sameSide l BG := by euclid_apply (helper_2_6_step7_sscl b c l CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_sshg : h.sameSide g DF := by euclid_apply (helper_2_6_step7_sshg b g h BG DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the parallelograms
  have step7_par1 : formParallelogram d m b h DF BG AB KM := by euclid_apply (helper_2_6_step7_par1 b d h m DF BG AB KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_par2 : formParallelogram h g l e BG CE KM EF := by euclid_apply (helper_2_6_step7_par2 e g h l BG CE KM EF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_cbhl : formParallelogram c b l h AB KM CE BG := by euclid_apply (helper_2_6_step7_cbhl b c h l AB KM CE BG (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_hmfg : formParallelogram h m g f KM EF BG DF := by euclid_apply (helper_2_6_step7_hmfg f g h m KM EF BG DF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- prop43 complement equality + the two area bridges
  have step7_compl : Triangle.area △ b:c:l + Triangle.area △ b:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by euclid_apply (helper_2_6_step7_compl b c d e f g h l m AB DE CE DF EF BG KM (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step7_lhs : Triangle.area △ c:b:h + Triangle.area △ c:h:l
      = Triangle.area △ b:c:l + Triangle.area △ b:l:h := by euclid_apply (helper_2_6_step7_lhs c b l h AB KM CE BG (by assumption)); (try split_ands) <;> assumption
  have step7_rhs : Triangle.area △ h:m:f + Triangle.area △ h:f:g
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by euclid_apply (helper_2_6_step7_rhs h m g f KM EF BG DF (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
