import SystemE
import Book.Prop43
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step15_ande
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step9_knab
import Book2.Prop04.step25_cab
import Book2.Prop04.step9_cnbe
import Book2.Prop04.step15_bnhk
import Book2.Prop04.step22_dnhk
import Book2.Prop04.step22_hnde
import Book2.Prop04.step9_cfbe
import Book2.Prop04.step22_hkde
import Book2.Prop04.step25_bead
import Book2.Prop04.step25_abde
import Book2.Prop04.step25_bchk2
import Book2.Prop04.step25_bigpar
import Book2.Prop04.step25_gnbe
import Book2.Prop04.step15_bke
import Book2.Prop04.step25_bchk
import Book2.Prop04.step25_ghde
import Book2.Prop04.step25_gfbe
import Book2.Prop04.step22_ahcf
import Book2.Prop04.step22_adni
import Book2.Prop04.step25_par1
import Book2.Prop04.step25_par2
import Book2.Prop04.step25_paracgh
import Book2.Prop04.step25_pargkef
import Book2.Prop04.step25_compl
import Book2.Prop04.step25_lhs
import Book2.Prop04.step25_rhs
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.25: the complements AG and GE of the square ADEB about diagonal BD are equal [Prop.~1.43].
   proposition_43 on ADEB (diagonal B-D through g), with inner parallelograms CGKB (`b k c g`) and
   HGFD (`g f h d`), gives △c:a:h + △c:h:g = △k:g:f + △k:f:e; the parallelogram_area bridges
   (step25_lhs on ACGH, step25_rhs on GKEF) recast this to △a:c:g + △a:g:h = △g:k:e + △g:e:f. -/
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
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step15_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_4_step15_ande a d AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_knab : ¬(k.onLine AB) := by euclid_apply (helper_2_4_step9_knab g k AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_cab : c.onLine AB := by euclid_apply (helper_2_4_step25_cab a b c AB (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_4_step9_cnbe a b c AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- h ≠ d (h ∈ HK, d ∉ HK) for step22_hnde
  have hABHK0 : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have hgd0 : g ≠ d := by euclid_finish
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step22_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_4_step22_hnde a d h AD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
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
  have step9_cfbe : ¬(CF.intersectsLine BE) := by euclid_apply (helper_2_4_step9_cfbe CF AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_hkde : ¬(HK.intersectsLine DE) := by euclid_apply (helper_2_4_step22_hkde HK DE AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_bead : ¬(BE.intersectsLine AD) := by euclid_apply (helper_2_4_step25_bead AD BE (by assumption)); (try split_ands) <;> assumption
  have step25_abde : ¬(AB.intersectsLine DE) := by euclid_apply (helper_2_4_step25_abde AB DE (by assumption)); (try split_ands) <;> assumption
  -- the big square ADEB as a parallelogram
  have hed2 : e ≠ d := by euclid_finish
  have step25_bchk2 : b.sameSide a DE := by euclid_apply (helper_2_4_step25_bchk2 b a AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_bigpar : formParallelogram b e a d BE AD AB DE := by euclid_apply (helper_2_4_step25_bigpar b e a d BE AD AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- distinctness of the foot points
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ step25_cab)
  -- g ∉ BE (g on CF ∥ BE), giving k ≠ g (k ∈ BE)
  have step25_gnbe : ¬(g.onLine BE) := by euclid_apply (helper_2_4_step25_gnbe g CF BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hkg : k ≠ g := fun hh => step25_gnbe (hh ▸ hkBE)
  -- foot betweenness on BE
  have step15_bke : between b k e := by euclid_apply (helper_2_4_step15_bke a b d e g k BE HK DE BD AB CF AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the four parallelograms
  have step25_bchk : b.sameSide c HK := by euclid_apply (helper_2_4_step25_bchk b c AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_ghde : g.sameSide h DE := by euclid_apply (helper_2_4_step25_ghde g h HK DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_gfbe : g.sameSide f BE := by euclid_apply (helper_2_4_step25_gfbe g f CF BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_ahcf : a.sameSide h CF := by euclid_apply (helper_2_4_step22_ahcf a h AD CF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hke : k ≠ e := by euclid_finish
  have hfd : f ≠ d := by euclid_finish
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by assumption)); (try split_ands) <;> assumption
  have step25_par1 : formParallelogram b k c g BE CF AB HK := by euclid_apply (helper_2_4_step25_par1 b k c g BE CF AB HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_par2 : formParallelogram g f h d CF AD HK DE := by euclid_apply (helper_2_4_step25_par2 g f h d CF AD HK DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_paracgh : formParallelogram a c h g AB HK AD CF := by euclid_apply (helper_2_4_step25_paracgh a c h g AB HK AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_pargkef : formParallelogram g k f e HK DE CF BE := by euclid_apply (helper_2_4_step25_pargkef g k f e HK DE CF BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_compl : Triangle.area △ c:a:h + Triangle.area △ c:h:g
      = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by euclid_apply (helper_2_4_step25_compl a b c d e f g h k AB CF AD BE HK BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step25_lhs : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      = Triangle.area △ c:a:h + Triangle.area △ c:h:g := by euclid_apply (helper_2_4_step25_lhs a c h g AB HK AD CF (by assumption)); (try split_ands) <;> assumption
  have step25_rhs : Triangle.area △ g:k:e + Triangle.area △ g:e:f
      = Triangle.area △ k:g:f + Triangle.area △ k:f:e := by euclid_apply (helper_2_4_step25_rhs g k e f HK DE CF BE (by assumption)); (try split_ands) <;> assumption
  rw [step25_lhs, step25_rhs, step25_compl]

end Elements.Book2
