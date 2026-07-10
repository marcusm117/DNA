import SystemE
import Book1.Prop43.Main
import Helpers.OffLine
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.6 [AFTER / inline-collapse measurement]: identical statement to step6.lean, but every off-line
   and sameSide fact that maps to a Book2/Helpers library lemma is proved INLINE by a one-line
   `euclid_apply (lemma …)` instead of a `have … := by sorry` backed by its own file. This deletes 11
   backing files and flattens the layer-1..layer-5 off-line/sameSide tree to a flat block.
   What STAYS as a real sub-fact: big_eoff (angle degeneracy), boffdg (AB=DG→CE chain), kmef/dgbf
   (proposition_30 parallels), and the parallelograms + area bridges (genuine content). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_inline (a b c d e f g h l m : Point) (AB BE CE BF EF DG KM : Line)
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
  -- ── facts that STAY (genuine degeneracy / chains / proposition_30 parallels) ──
  have step6_big_eoff : ¬(e.onLine AB) := by sorry
  have step6_boffdg : ¬(b.onLine DG) := by sorry
  have step6_kmef : ¬(KM.intersectsLine EF) := by sorry
  have step6_dgbf : ¬(DG.intersectsLine BF) := by sorry
  -- ── INLINE library calls (was 11 backing files; now zero) ──
  have step6_doffce : ¬(d.onLine CE) := by
    have hdc : d ≠ c := by euclid_finish
    exact offLine_of_two_points d c e AB CE hdAB hcAB hdc hcCE heCE step6_big_eoff
  have step6_boffef : ¬(b.onLine EF) :=
    offLine_of_parallel b e AB EF hbAB heEF step6_big_eoff hEFAB
  have step6_bmf_hoffab : ¬(h.onLine AB) := by
    have hhb : h ≠ b := fun heq => step6_boffdg (heq ▸ hhDG)
    exact offLine_of_two_points' h b e BE AB hhBE hbBE hhb hbAB heBE step6_big_eoff
  have step6_eoffdg : ¬(e.onLine DG) := by
    have hdoffCE : ¬(d.onLine CE) := step6_doffce
    exact offLine_of_parallel e d CE DG heCE hdDG hdoffCE hDGCE
  have step6_hoffef : ¬(h.onLine EF) := by
    have hhe : h ≠ e := fun heq => step6_eoffdg (heq ▸ hhDG)
    exact offLine_of_two_points' h e b BE EF hhBE heBE hhe heEF hbBE step6_boffef
  have step6_doffbf : ¬(d.onLine BF) :=
    offLine_of_parallel' d b DG BF hdDG hbBF step6_boffdg step6_dgbf
  have step6_hoffbf : ¬(h.onLine BF) :=
    offLine_of_parallel' h b DG BF hhDG hbBF step6_boffdg step6_dgbf
  have step6_foffkm : ¬(f.onLine KM) :=
    offLine_of_parallel f h EF KM hfEF hhKM step6_hoffef step6_kmef
  have step6_ssbd : b.sameSide d KM :=
    sameSide_of_parallel b d h AB KM hbAB hdAB hhKM step6_bmf_hoffab hKMAB
  have step6_sscl : c.sameSide l DG :=
    sameSide_of_parallel c l d CE DG hcCE hlCE hdDG step6_doffce hDGCE
  have step6_sshg : h.sameSide g BF :=
    sameSide_of_parallel' h g d DG BF hhDG hgDG hdDG step6_doffbf step6_dgbf
  have step6_sshl : h.sameSide l EF :=
    sameSide_of_parallel' h l h KM EF hhKM hlKM hhKM step6_hoffef step6_kmef
  -- ── genuine content (parallelograms + area bridges) — unchanged from BEFORE ──
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
