import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.25: the complements AG and GE of the square ADEB about diagonal BD are equal [Prop.~1.43].
   proposition_43 on ADEB (diagonal B-D through g), with inner parallelograms CGKB (`b k c g`) and
   HGFD (`g f h d`), gives △c:a:h + △c:h:g = △k:g:f + △k:f:e; the parallelogram_area bridges
   (step25_lhs on ACGH, step25_rhs on GKEF) recast this to △a:c:g + △a:g:h = △g:k:e + △g:e:f. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step25 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hkBE : k.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) (hstep8 : |(b─c)| = |(c─g)|) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = Triangle.area △ g:k:e + Triangle.area △ g:e:f := by
  euclid_intros
  -- off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hda : d ≠ a := fun hh => had hh.symm
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  have step15_ande : ¬(a.onLine DE) := by sorry
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  have step9_knab : ¬(k.onLine AB) := by sorry
  have step25_cab : c.onLine AB := by sorry
  have step9_cnbe : ¬(c.onLine BE) := by sorry
  -- h ≠ d (h ∈ HK, d ∉ HK) for step22_hnde
  have hABHK0 : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hgd0 : g ≠ d := by euclid_finish
  have step15_bnhk : ¬(b.onLine HK) := by sorry
  have step22_dnhk : ¬(d.onLine HK) := by sorry
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step22_hnde : ¬(h.onLine DE) := by sorry
  -- line distinctness
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hBEAD : BE ≠ AD := fun hh => step9_anbe (hh ▸ haAD)
  have hCFBE : CF ≠ BE := fun hh => step9_cnbe (hh ▸ hcCF)
  have hBECF : BE ≠ CF := fun hh => hCFBE hh.symm
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hDEAB' : DE ≠ AB := fun hh => step8_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have hHKDE : HK ≠ DE := fun hh => step22_hnde (hh ▸ hhHK)
  -- non-intersections (parallel transitivity) + symmetric orientations
  have step9_cfbe : ¬(CF.intersectsLine BE) := by sorry
  have step22_hkde : ¬(HK.intersectsLine DE) := by sorry
  have step25_bead : ¬(BE.intersectsLine AD) := by sorry
  have step25_abde : ¬(AB.intersectsLine DE) := by sorry
  -- the big square ADEB as a parallelogram
  have hed2 : e ≠ d := by euclid_finish
  have step25_bchk2 : b.sameSide a DE := by sorry
  have step25_bigpar : formParallelogram b e a d BE AD AB DE := by sorry
  -- distinctness of the foot points
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  -- g ∉ BE (g on CF ∥ BE), giving k ≠ g (k ∈ BE)
  have step25_gnbe : ¬(g.onLine BE) := by sorry
  have hkg : k ≠ g := fun hh => step25_gnbe (hh ▸ hkBE)
  -- foot betweenness on BE
  have step15_bke : between b k e := by sorry
  -- the four parallelograms
  have step25_bchk : b.sameSide c HK := by sorry
  have step25_ghde : g.sameSide h DE := by sorry
  have step25_gfbe : g.sameSide f BE := by sorry
  have step22_ahcf : a.sameSide h CF := by sorry
  have hke : k ≠ e := by euclid_finish
  have hfd : f ≠ d := by euclid_finish
  have step22_adni : ¬(AD.intersectsLine CF) := by sorry
  have step25_par1 : formParallelogram b k c g BE CF AB HK := by sorry
  have step25_par2 : formParallelogram g f h d CF AD HK DE := by sorry
  have step25_paracgh : formParallelogram a c h g AB HK AD CF := by sorry
  have step25_pargkef : formParallelogram g k f e HK DE CF BE := by sorry
  have step25_compl : Triangle.area △ c:a:h + Triangle.area △ c:h:g
      = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by sorry
  have step25_lhs : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      = Triangle.area △ c:a:h + Triangle.area △ c:h:g := by sorry
  have step25_rhs : Triangle.area △ g:k:e + Triangle.area △ g:e:f
      = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by sorry
  rw [step25_lhs, step25_rhs, step25_compl]

end Elements.Book2
