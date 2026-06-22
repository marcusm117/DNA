import SystemE
import Book2.Prop07.step9_bfbc
import Book2.Prop07.step3_dnab
import Book2.Prop07.step3_bgd
import Book2.Prop07.step3_gnab
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_anbe
import Book2.Prop07.step8_ahd
import Book2.Prop07.step8_hab
import Book2.Prop07.step4_ahbe
import Book2.Prop07.step8_hsa
import Book2.Prop07.step4_parAF
import Book2.Prop07.step8_parAF2
import Book2.Prop07.step8_rectAF
import Book2.Prop07.step8_lens
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.8: double AF is twice the rectangle contained by AB and BC. AF = ABFH = |h─f|·|h─a|
   (rectAF, via rectangle_area with the right angle ∠h:a:b); the opposite sides give |h─f| = |a─b|
   and |h─a| = |b─f| (lens, Prop.~1.34'), and |b─f| = |b─c| (step9). Hence AF = |a─b|·|b─c| and
   2 AF = 2 (|a─b|·|b─c|). -/
theorem helper_2_7_step8 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
        + (Triangle.area △ a:b:f + Triangle.area △ a:f:h)
      = |(a─b)| * |(b─c)| + |(a─b)| * |(b─c)| := by
  euclid_intros
  have step9_bfbc : |(b─f)| = |(b─c)| := by euclid_apply (helper_2_7_step9_bfbc a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_7_step3_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := by euclid_finish
  have step3_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_7_step3_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have hfb : f ≠ b := fun hh => hbf hh.symm
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have step3_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_7_step3_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  -- foot h between a and d, giving the right angle ∠h:a:b
  have step8_ahd : between a h d := by euclid_apply (helper_2_7_step8_ahd a b d g h AB HF BD AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_hab : ∠ h:a:b = ∟ := by euclid_apply (helper_2_7_step8_hab a b d h AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the rectangle ABFH (two orientations) + its side lengths
  have step4_ahbe : a.sameSide h BE := by euclid_apply (helper_2_7_step4_ahbe a h AD BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_hsa : h.sameSide a BE := by euclid_apply (helper_2_7_step8_hsa h a AD BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by euclid_apply (helper_2_7_step4_parAF a b h f AB HF AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_parAF2 : formParallelogram h f a b HF AB AD BE := by euclid_apply (helper_2_7_step8_parAF2 h f a b HF AB AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_rectAF : Triangle.area △ a:b:f + Triangle.area △ a:f:h = |(h─f)| * |(h─a)| := by euclid_apply (helper_2_7_step8_rectAF h f a b HF AB AD BE (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_lens : |(a─b)| = |(h─f)| ∧ |(a─h)| = |(b─f)| := by euclid_apply (helper_2_7_step8_lens a b h f AB HF AD BE (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
