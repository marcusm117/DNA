import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7: the complements CBHL and HMFG of the square CEFD about diagonal DE are equal [Prop.~1.43].
   proposition_43 on CEFD (diagonal D-E through h), with the two parallelograms ABOUT the diagonal
   (DMBH at corner D = `d m b h`, HGLE at corner E = `h g l e`), yields
   △b:c:l + △b:l:h = △m:h:g + △m:g:f. The parallelogram_area bridges (step7_lhs on CBHL, step7_rhs on
   HMFG) recast those to the goal's triangulation △c:b:h + △c:h:l = △h:m:f + △h:f:g. -/
set_option systemE.solverTime 30 in
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
  have step2_eoff : ¬(e.onLine AB) := by sorry
  have step7_foffab : ¬(f.onLine AB) := by sorry
  have step6_hoffab : ¬(h.onLine AB) := by sorry
  have step7_boffce : ¬(b.onLine CE) := by sorry
  have step7_coffdf : ¬(c.onLine DF) := by sorry
  have step7_boffdf : ¬(b.onLine DF) := by sorry
  have step7_hoffef : ¬(h.onLine EF) := by sorry
  -- shared line-distinctness + parallels
  have step7_efne : EF ≠ AB := by sorry
  have step7_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step7_bgdf : ¬(BG.intersectsLine DF) := by sorry
  -- derived off-line facts (need the parallels above)
  have step7_hoffdf : ¬(h.onLine DF) := by sorry
  have step7_eoffbg : ¬(e.onLine BG) := by sorry
  have step7_foffkm : ¬(f.onLine KM) := by sorry
  have step7_doffkm : ¬(d.onLine KM) := by sorry
  -- the square
  have step7_big : formParallelogram d f c e DF CE AB EF := by sorry
  -- foot betweenness between d m f (cone: opposite-sides of d,f across KM)
  have step7_boffde : ¬(b.onLine DE) := by sorry
  have step7_sscebg : c.sameSide e BG := by sorry
  have step7_cnsdBG : ¬(c.sameSide d BG) := by sorry
  have step7_dnseBG : ¬(d.sameSide e BG) := by sorry
  have step7_dhe : between d h e := by sorry
  have step7_dnse : ¬(d.sameSide e KM) := by sorry
  have step7_essf : e.sameSide f KM := by sorry
  have step7_dnsf : ¬(d.sameSide f KM) := by sorry
  have step7_dmf : between d m f := by sorry
  -- the four sameSides (Family-3, two points on a parallel)
  have step7_ssdb : d.sameSide b KM := by sorry
  have step7_sshl : h.sameSide l EF := by sorry
  have step7_sscl : c.sameSide l BG := by sorry
  have step7_sshg : h.sameSide g DF := by sorry
  -- the parallelograms
  have step7_par1 : formParallelogram d m b h DF BG AB KM := by sorry
  have step7_par2 : formParallelogram h g l e BG CE KM EF := by sorry
  have step7_cbhl : formParallelogram c b l h AB KM CE BG := by sorry
  have step7_hmfg : formParallelogram h m g f KM EF BG DF := by sorry
  -- prop43 complement equality + the two area bridges
  have step7_compl : Triangle.area △ b:c:l + Triangle.area △ b:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by sorry
  have step7_lhs : Triangle.area △ c:b:h + Triangle.area △ c:h:l
      = Triangle.area △ b:c:l + Triangle.area △ b:l:h := by sorry
  have step7_rhs : Triangle.area △ h:m:f + Triangle.area △ h:f:g
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by sorry
  euclid_finish

end Elements.Book2
