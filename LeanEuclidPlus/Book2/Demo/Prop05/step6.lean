import SystemE
import Book.Prop43
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
set_option systemE.solverTime 30 in
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
  have step6_big_eoff : ¬(e.onLine AB) := by sorry
  have step6_doffce : ¬(d.onLine CE) := by sorry
  have step6_boffef : ¬(b.onLine EF) := by sorry
  have step6_boffdg : ¬(b.onLine DG) := by sorry
  have step6_bmf_hoffab : ¬(h.onLine AB) := by sorry
  have step6_eoffdg : ¬(e.onLine DG) := by sorry
  -- layer 2: off-line depending on layer 1
  have step6_hoffef : ¬(h.onLine EF) := by sorry
  -- layer 3: parallels (proposition_30) depending on the off-line anchors
  have step6_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step6_dgbf : ¬(DG.intersectsLine BF) := by sorry
  -- layer 4: off-line depending on the parallels
  have step6_doffbf : ¬(d.onLine BF) := by sorry
  have step6_hoffbf : ¬(h.onLine BF) := by sorry
  have step6_foffkm : ¬(f.onLine KM) := by sorry
  -- layer 5: sameSides depending on the off-line/parallel anchors
  have step6_ssbd : b.sameSide d KM := by sorry
  have step6_sscl : c.sameSide l DG := by sorry
  have step6_sshg : h.sameSide g BF := by sorry
  have step6_sshl : h.sameSide l EF := by sorry
  -- @args: a b c d e f AB BF CE EF
  have step6_big : formParallelogram b f c e BF CE AB EF := by sorry
  have step6_bmf : between b m f := by sorry
  have step6_par1 : formParallelogram b m d h BF DG AB KM := by sorry
  have step6_par2 : formParallelogram h g l e DG CE KM EF := by sorry
  have step6_cdhl : formParallelogram c d l h AB KM CE DG := by sorry
  have step6_hmfg : formParallelogram h m g f KM EF DG BF := by sorry
  have step6_compl : Triangle.area △ d:c:l + Triangle.area △ d:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by sorry
  have step6_lhs : Triangle.area △ c:d:h + Triangle.area △ c:h:l
      = Triangle.area △ d:c:l + Triangle.area △ d:l:h := by sorry
  have step6_rhs : Triangle.area △ h:m:f + Triangle.area △ h:f:g
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by sorry
  euclid_finish

end Elements.Book2
