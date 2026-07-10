import SystemE
import Book1.Prop43.Main
import Book2.Prop05.step6_big_eoff
import Book2.Prop05.step6_doffce
import Book2.Prop05.step6_boffef
import Book2.Prop05.step6_boffdg
import Book2.Prop05.step6_bmf_hoffab
import Book2.Prop05.step6_eoffdg
import Book2.Prop05.step6_hoffef
import Book2.Prop05.step6_kmef
import Book2.Prop05.step6_dgbf
import Book2.Prop05.step6_doffbf
import Book2.Prop05.step6_hoffbf
import Book2.Prop05.step6_foffkm
import Book2.Prop05.step6_ssbd
import Book2.Prop05.step6_sscl
import Book2.Prop05.step6_sshg
import Book2.Prop05.step6_sshl
import Book2.Prop05.step6_big
import Book2.Prop05.step6_bmf
import Book2.Prop05.step6_par1
import Book2.Prop05.step6_par2
import Book2.Prop05.step6_cdhl
import Book2.Prop05.step6_hmfg
import Book2.Prop05.step6_compl
import Book2.Prop05.step6_lhs
import Book2.Prop05.step6_rhs
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.6: the complements CDHL and HMFG of the square CEFB about diagonal BE are equal [Prop.~1.43].
   proposition_43 on CEFB (diagonal B-E through h), with the two parallelograms ABOUT the diagonal
   (BMDH at corner B = `b m d h`, HGLE at corner E = `h g l e`), yields
   △d:c:l + △d:l:h = △m:h:g + △m:g:f (the two complements, split along their B-E-ward diagonals).
   The parallelogram_area bridges (step6_lhs on CDHL, step6_rhs on HMFG) recast those to the goal's
   triangulation △c:d:h + △c:h:l = △h:m:f + △h:f:g. -/
theorem helper_2_5_step6 (a b c d e f g h l m : Point) (AB BE CE BF EF DG KM : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hmBF : m.onLine BF)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hgEF : g.onLine EF)
    (hdDG : d.onLine DG) (hgDG : g.onLine DG) (hhDG : h.onLine DG)
    (hhKM : h.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hacd : between a c d) (hcdb : between c d b) (hcelen : |(c─e)| = |(c─b)|)
    (hCEBF : ¬(CE.intersectsLine BF)) (hEFAB : ¬(EF.intersectsLine AB))
    (hDGCE : ¬(DG.intersectsLine CE)) (hKMAB : ¬(KM.intersectsLine AB))
    (hbce : ∠ b:c:e = ∟) (hcef : ∠ c:e:f = ∟) (hcbf : ∠ c:b:f = ∟) (hbfe : ∠ b:f:e = ∟)
    (hecBF : e.sameSide c BF) :
    Triangle.area △ c:d:h + Triangle.area △ c:h:l = Triangle.area △ h:m:f + Triangle.area △ h:f:g := by
  euclid_intros
  -- hoisted anchor facts (sibling sub-nodes) — supplied to the pgram/bmf helpers via assumption.
  -- layer 1: pure off-line leaves (need only Main facts)
  have step6_big_eoff : ¬(e.onLine AB) := by euclid_apply (helper_2_5_step6_big_eoff b c d e AB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)))
  have step6_doffce : ¬(d.onLine CE) := by euclid_apply (helper_2_5_step6_doffce a b c d e AB CE (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)))
  have step6_boffef : ¬(b.onLine EF) := by euclid_apply (helper_2_5_step6_boffef a b c d e AB CE EF (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have step6_boffdg : ¬(b.onLine DG) := by euclid_apply (helper_2_5_step6_boffdg b c d AB CE DG (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)))
  have step6_bmf_hoffab : ¬(h.onLine AB) := by euclid_apply (helper_2_5_step6_bmf_hoffab b e h AB BE DG (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(e.onLine AB); assumption)) (by euclid_assumption "" (show ¬(b.onLine DG); assumption)))
  have step6_eoffdg : ¬(e.onLine DG) := by euclid_apply (helper_2_5_step6_eoffdg d e CE DG (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  -- layer 2: off-line depending on layer 1
  have step6_hoffef : ¬(h.onLine EF) := by euclid_apply (helper_2_5_step6_hoffef b e h BE EF DG (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(b.onLine EF); assumption)) (by euclid_assumption "" (show ¬(e.onLine DG); assumption)))
  -- layer 3: parallels (proposition_30) depending on the off-line anchors
  have step6_kmef : ¬(KM.intersectsLine EF) := by euclid_apply (helper_2_5_step6_kmef e h AB KM EF (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(e.onLine AB); assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)))
  have step6_dgbf : ¬(DG.intersectsLine BF) := by euclid_apply (helper_2_5_step6_dgbf b c d DG CE BF AB (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)))
  -- layer 4: off-line depending on the parallels
  have step6_doffbf : ¬(d.onLine BF) := by euclid_apply (helper_2_5_step6_doffbf b d DG BF (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show ¬(b.onLine DG); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)))
  have step6_hoffbf : ¬(h.onLine BF) := by euclid_apply (helper_2_5_step6_hoffbf b h DG BF (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show ¬(b.onLine DG); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)))
  have step6_foffkm : ¬(f.onLine KM) := by euclid_apply (helper_2_5_step6_foffkm f h EF KM (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)))
  -- layer 5: sameSides depending on the off-line/parallel anchors
  have step6_ssbd : b.sameSide d KM := by euclid_apply (helper_2_5_step6_ssbd b d h AB KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  have step6_sscl : c.sameSide l DG := by euclid_apply (helper_2_5_step6_sscl c d l CE DG (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show ¬(d.onLine CE); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step6_sshg : h.sameSide g BF := by euclid_apply (helper_2_5_step6_sshg d g h DG BF (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show ¬(d.onLine BF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)))
  have step6_sshl : h.sameSide l EF := by euclid_apply (helper_2_5_step6_sshl h l KM EF (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)))
  -- @args: a b c d e f AB BF CE EF
  have step6_big : formParallelogram b f c e BF CE AB EF := by euclid_apply (helper_2_5_step6_big a b c d e f AB BF CE EF (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show between a c d; assumption)) (by euclid_assumption "" (show between c d b; assumption)) (by euclid_assumption "" (show |(c─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)) (by euclid_assumption "" (show ∠ b:c:e = ∟; assumption)))
  have step6_bmf : between b m f := by euclid_apply (helper_2_5_step6_bmf b c d e f h m AB BF BE EF CE DG KM (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine EF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)) (by euclid_assumption "" (show ¬(e.onLine DG); assumption)) (by euclid_assumption "" (show ¬(b.onLine DG); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(EF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CE.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)) (by euclid_assumption "" (show between c d b; assumption)))
  have step6_par1 : formParallelogram b m d h BF DG AB KM := by euclid_apply (helper_2_5_step6_par1 b d h m BF DG AB KM (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show ¬(h.onLine BF); assumption)) (by euclid_assumption "" (show b.sameSide d KM; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)))
  have step6_par2 : formParallelogram h g l e DG CE KM EF := by euclid_apply (helper_2_5_step6_par2 e g h l DG CE KM EF (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show ¬(e.onLine DG); assumption)) (by euclid_assumption "" (show h.sameSide l EF; assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)))
  have step6_cdhl : formParallelogram c d l h AB KM CE DG := by euclid_apply (helper_2_5_step6_cdhl c d h l AB KM CE DG (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine AB; assumption)) (by euclid_assumption "" (show l.onLine KM; assumption)) (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show l.onLine CE; assumption)) (by euclid_assumption "" (show d.onLine DG; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show ¬(h.onLine AB); assumption)) (by euclid_assumption "" (show c.sameSide l DG; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine CE); assumption)))
  have step6_hmfg : formParallelogram h m g f KM EF DG BF := by euclid_apply (helper_2_5_step6_hmfg f g h m KM EF DG BF (by euclid_assumption "" (show h.onLine KM; assumption)) (by euclid_assumption "" (show m.onLine KM; assumption)) (by euclid_assumption "" (show g.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine DG; assumption)) (by euclid_assumption "" (show g.onLine DG; assumption)) (by euclid_assumption "" (show m.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine KM); assumption)) (by euclid_assumption "" (show h.sameSide g BF; assumption)) (by euclid_assumption "" (show ¬(KM.intersectsLine EF); assumption)) (by euclid_assumption "" (show ¬(DG.intersectsLine BF); assumption)))
  have step6_compl : Triangle.area △ d:c:l + Triangle.area △ d:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by euclid_apply (helper_2_5_step6_compl b c d e f g h l m AB BE CE BF EF DG KM (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show e.sameSide c BF; assumption)) (by euclid_assumption "" (show formParallelogram b f c e BF CE AB EF; assumption)) (by euclid_assumption "" (show between b m f; assumption)) (by euclid_assumption "" (show formParallelogram b m d h BF DG AB KM; assumption)) (by euclid_assumption "" (show formParallelogram h g l e DG CE KM EF; assumption)))
  have step6_lhs : Triangle.area △ c:d:h + Triangle.area △ c:h:l
      = Triangle.area △ d:c:l + Triangle.area △ d:l:h := by euclid_apply (helper_2_5_step6_lhs c d l h AB KM CE DG (by euclid_assumption "" (show formParallelogram c d l h AB KM CE DG; assumption)))
  have step6_rhs : Triangle.area △ h:m:f + Triangle.area △ h:f:g
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by euclid_apply (helper_2_5_step6_rhs h m g f KM EF DG BF (by euclid_assumption "" (show formParallelogram h m g f KM EF DG BF; assumption)))
  euclid_finish

end Elements.Book2
