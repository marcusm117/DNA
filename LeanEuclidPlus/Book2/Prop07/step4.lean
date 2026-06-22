import SystemE
import Book2.Prop07.step3_cnad
import Book2.Prop07.step3_dnab
import Book2.Prop07.step3_anbe
import Book2.Prop07.step3_bgd
import Book2.Prop07.step3_gnab
import Book2.Prop07.step3_cab
import Book2.Prop07.step3_cnbe
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_dnhf
import Book2.Prop07.step3_ande
import Book2.Prop07.step3_hnde
import Book2.Prop07.step3_cfbe
import Book2.Prop07.step3_hkde
import Book2.Prop07.step3_abde
import Book2.Prop07.step4_hgf
import Book2.Prop07.step4_cgn
import Book2.Prop07.step3_bke
import Book2.Prop07.step3_gnbe
import Book2.Prop07.step4_ahbe
import Book2.Prop07.step4_cbde
import Book2.Prop07.step4_parAF
import Book2.Prop07.step4_parCE
import Book2.Prop07.step4_tileAF
import Book2.Prop07.step4_tileCE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.4: the whole AF is equal to the whole CE. Adding the square CF to both sides of the
   complement equality AG = GE (step3): AF = AG + CF (tileAF) and CE = CF + GE (tileCE), so
   AF = AG + CF = GE + CF = CE. The tilings come from sum_parallelograms_area on the two half-
   rectangles ABFH and CBEN, cut by the internal lines CN (between h g f / c g n) and HF. -/
theorem helper_2_7_step4 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep3 : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      = Triangle.area △ g:f:e + Triangle.area △ g:e:n) :
    Triangle.area △ a:b:f + Triangle.area △ a:f:h = Triangle.area △ c:b:e + Triangle.area △ c:e:n := by
  euclid_intros
  -- off-line / distinctness roots (shared with step3's preamble)
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step3_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_7_step3_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_7_step3_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_7_step3_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have step3_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_7_step3_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_cab : c.onLine AB := by euclid_apply (helper_2_7_step3_cab a b c AB (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_7_step3_cnbe a b c e AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hgd0 : g ≠ d := by euclid_finish
  have step3_dnhf : ¬(d.onLine HF) := by euclid_apply (helper_2_7_step3_dnhf b d g BD HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_7_step3_ande a d AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hhd : h ≠ d := fun hh => step3_dnhf (hh ▸ hhHF)
  have step3_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_7_step3_hnde a b d g h AB AD HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  have hBEAD : BE ≠ AD := fun hh => hADBE' hh.symm
  -- non-intersections (parallel transitivity)
  have step3_cfbe : ¬(CN.intersectsLine BE) := by euclid_apply (helper_2_7_step3_cfbe a CN AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_hkde : ¬(HF.intersectsLine DE) := by euclid_apply (helper_2_7_step3_hkde HF DE AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_abde : ¬(AB.intersectsLine DE) := by euclid_apply (helper_2_7_step3_abde AB DE (by assumption)); (try split_ands) <;> assumption
  -- betweenness of the foot points on the internal lines
  have step4_hgf : between h g f := by euclid_apply (helper_2_7_step4_hgf a b c d h g f AB CN AD BE HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_cgn : between c g n := by euclid_apply (helper_2_7_step4_cgn b c d n g AB DE HF BD CN (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bke : between b f e := by euclid_apply (helper_2_7_step3_bke a b d e g f BE HF DE BD AB CN AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- distinctness for the parallelograms
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_gnbe : ¬(g.onLine BE) := by euclid_apply (helper_2_7_step3_gnbe g CN BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hne : n ≠ e := by euclid_finish
  -- the two half-rectangles and the same-side facts they need
  have step4_ahbe : a.sameSide h BE := by euclid_apply (helper_2_7_step4_ahbe a h AD BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_cbde : c.sameSide b DE := by euclid_apply (helper_2_7_step4_cbde c b AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by euclid_apply (helper_2_7_step4_parAF a b h f AB HF AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_parCE : formParallelogram c n b e CN BE AB DE := by euclid_apply (helper_2_7_step4_parCE c n b e CN BE AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the two tilings
  have step4_tileAF : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      = Triangle.area △ a:b:f + Triangle.area △ a:f:h := by euclid_apply (helper_2_7_step4_tileAF a b c h g f AB HF AD BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_tileCE : (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
      = Triangle.area △ c:b:e + Triangle.area △ c:e:n := by euclid_apply (helper_2_7_step4_tileCE c n b e g f CN BE AB DE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
