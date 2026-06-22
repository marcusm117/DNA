import SystemE
import Book2.Prop07.step3_cnad
import Book2.Prop07.step3_dnab
import Book2.Prop07.step3_anbe
import Book2.Prop07.step3_ande
import Book2.Prop07.step3_bgd
import Book2.Prop07.step3_gnab
import Book2.Prop07.step3_cab
import Book2.Prop07.step3_cnbe
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_dnhf
import Book2.Prop07.step3_hnde
import Book2.Prop07.step3_cfbe
import Book2.Prop07.step3_hkde
import Book2.Prop07.step3_bead
import Book2.Prop07.step3_abde
import Book2.Prop07.step3_bchk2
import Book2.Prop07.step3_bigpar
import Book2.Prop07.step3_gnbe
import Book2.Prop07.step3_bke
import Book2.Prop07.step3_bchk
import Book2.Prop07.step3_ghde
import Book2.Prop07.step3_gfbe
import Book2.Prop07.step3_ahcf
import Book2.Prop07.step3_par1
import Book2.Prop07.step3_par2
import Book2.Prop07.step3_paracgh
import Book2.Prop07.step3_pargkef
import Book2.Prop07.step3_compl
import Book2.Prop07.step3_lhs
import Book2.Prop07.step3_rhs
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3: the complements AG and GE of the square ADEB about diagonal BD are equal [Prop.~1.43].
   proposition_43 on ADEB (diagonal B-D through g), with inner parallelograms CGFB (`b f c g`) and
   HGND (`g n h d`), gives △c:a:h + △c:h:g = △f:g:n + △f:n:e; the parallelogram_area bridges
   (step3_lhs on ACGH, step3_rhs on GFEN) recast this to △a:c:g + △a:g:h = △g:f:e + △g:e:n. -/
theorem helper_2_7_step3 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCNAD : ¬(CN.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟) :
    Triangle.area △ a:c:g + Triangle.area △ a:g:h = Triangle.area △ g:f:e + Triangle.area △ g:e:n := by
  euclid_intros
  -- off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hda : d ≠ a := fun hh => had hh.symm
  have step3_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_7_step3_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_7_step3_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_7_step3_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_7_step3_ande a d AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have step3_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_7_step3_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_cab : c.onLine AB := by euclid_apply (helper_2_7_step3_cab a b c AB (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_7_step3_cnbe a b c e AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- h ≠ d (h ∈ HF, d ∉ HF)
  have hABHF0 : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hgd0 : g ≠ d := by euclid_finish
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_dnhf : ¬(d.onLine HF) := by euclid_apply (helper_2_7_step3_dnhf b d g BD HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hhd : h ≠ d := fun hh => step3_dnhf (hh ▸ hhHF)
  have step3_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_7_step3_hnde a b d g h AB AD HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hBEAD : BE ≠ AD := fun hh => step3_anbe (hh ▸ haAD)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hBECN : BE ≠ CN := fun hh => hCNBE hh.symm
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  -- non-intersections (parallel transitivity) + symmetric orientations
  have step3_cfbe : ¬(CN.intersectsLine BE) := by euclid_apply (helper_2_7_step3_cfbe a CN AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_hkde : ¬(HF.intersectsLine DE) := by euclid_apply (helper_2_7_step3_hkde HF DE AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bead : ¬(BE.intersectsLine AD) := by euclid_apply (helper_2_7_step3_bead AD BE (by assumption)); (try split_ands) <;> assumption
  have step3_abde : ¬(AB.intersectsLine DE) := by euclid_apply (helper_2_7_step3_abde AB DE (by assumption)); (try split_ands) <;> assumption
  -- the big square ADEB as a parallelogram
  have hed2 : e ≠ d := by euclid_finish
  have step3_bchk2 : b.sameSide a DE := by euclid_apply (helper_2_7_step3_bchk2 b a AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bigpar : formParallelogram b e a d BE AD AB DE := by euclid_apply (helper_2_7_step3_bigpar b e a d BE AD AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- distinctness of the foot points
  have hcg : c ≠ g := fun hh => step3_gnab (hh ▸ step3_cab)
  -- g ∉ BE (g on CN ∥ BE), giving f ≠ g (f ∈ BE)
  have step3_gnbe : ¬(g.onLine BE) := by euclid_apply (helper_2_7_step3_gnbe g CN BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hfg : f ≠ g := fun hh => step3_gnbe (hh ▸ hfBE)
  -- foot betweenness on BE
  have step3_bke : between b f e := by euclid_apply (helper_2_7_step3_bke a b d e g f BE HF DE BD AB CN AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the four parallelograms
  have step3_bchk : b.sameSide c HF := by euclid_apply (helper_2_7_step3_bchk b c AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_ghde : g.sameSide h DE := by euclid_apply (helper_2_7_step3_ghde g h HF DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_gfbe : g.sameSide n BE := by euclid_apply (helper_2_7_step3_gfbe g n CN BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_ahcf : a.sameSide h CN := by euclid_apply (helper_2_7_step3_ahcf a h AD CN (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hfe : f ≠ e := by euclid_finish
  have hnd : n ≠ d := by euclid_finish
  have step3_par1 : formParallelogram b f c g BE CN AB HF := by euclid_apply (helper_2_7_step3_par1 b f c g BE CN AB HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_par2 : formParallelogram g n h d CN AD HF DE := by euclid_apply (helper_2_7_step3_par2 g n h d CN AD HF DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_paracgh : formParallelogram a c h g AB HF AD CN := by euclid_apply (helper_2_7_step3_paracgh a c h g AB HF AD CN (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_pargkef : formParallelogram g f n e HF DE CN BE := by euclid_apply (helper_2_7_step3_pargkef g f n e HF DE CN BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_compl : Triangle.area △ c:a:h + Triangle.area △ c:h:g
      = Triangle.area △ f:g:n + Triangle.area △ f:n:e := by euclid_apply (helper_2_7_step3_compl a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_lhs : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      = Triangle.area △ c:a:h + Triangle.area △ c:h:g := by euclid_apply (helper_2_7_step3_lhs a c h g AB HF AD CN (by assumption)); (try split_ands) <;> assumption
  have step3_rhs : Triangle.area △ g:f:e + Triangle.area △ g:e:n
      = Triangle.area △ f:g:n + Triangle.area △ f:n:e := by euclid_apply (helper_2_7_step3_rhs g f e n HF DE CN BE (by assumption)); (try split_ands) <;> assumption
  rw [step3_lhs, step3_rhs, step3_compl]

end Elements.Book2
