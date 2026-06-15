import SystemE
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_gnab
import Book2.Prop04.step15_bnhk
import Book2.Prop04.step22_anhk
import Book2.Prop04.step22_dnhk
import Book2.Prop04.step22_abshk
import Book2.Prop04.step22_ahd
import Book2.Prop04.step22_hsd
import Book2.Prop04.step15_ande
import Book2.Prop04.step22_hnde
import Book2.Prop04.step22_hkde
import Book2.Prop04.step22_gf
import Book2.Prop04.step22_adni
import Book2.Prop04.step22_par
import Book2.Prop04.step24_hf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.24: the squares HF and KC are on AC and CB — area(HGFD) = |a─c|² and area(CGKB) = |c─b|².
   The second is step21. The first is step24_hf (rectangle_area on the parallelogram HGFD with side
   |h─g| = |a─c|), for which the HGFD parallelogram (step22_par) is re-derived from the figure. -/
theorem helper_2_4_step24 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep8 : |(b─c)| = |(c─g)|)
    (hstep21 : Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|)
    (hstep22 : (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)))
    (hstep23 : |(h─g)| = |(a─c)|) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)|) ∧
      (Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)|) := by
  euclid_intros
  -- re-derive the HGFD parallelogram (same preamble as step22)
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_4_step9_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ hcAB)
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hgd : g ≠ d := by euclid_finish
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  have step15_bnhk : ¬(b.onLine HK) := by euclid_apply (helper_2_4_step15_bnhk b g AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_anhk : ¬(a.onLine HK) := by euclid_apply (helper_2_4_step22_anhk a g AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_dnhk : ¬(d.onLine HK) := by euclid_apply (helper_2_4_step22_dnhk b d g BD HK (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_abshk : a.sameSide b HK := by euclid_apply (helper_2_4_step22_abshk a b AB HK (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_ahd : between a h d := by euclid_apply (helper_2_4_step22_ahd a b d g h AD HK BD AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_hsd : h.sameSide d CF := by euclid_apply (helper_2_4_step22_hsd h d AD CF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- HK ∥ DE preamble: h ∉ DE ⟹ HK ≠ DE; d ∉ AB ⟹ DE ≠ AB
  have hhd : h ≠ d := fun hh => step22_dnhk (hh ▸ hhHK)
  have step15_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_4_step15_ande a d AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_4_step22_hnde a d h AD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hHKDE : HK ≠ DE := fun hh => step22_hnde (hh ▸ hhHK)
  have hDEAB' : DE ≠ AB := fun hh => step8_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have step22_hkde : ¬(HK.intersectsLine DE) := by euclid_apply (helper_2_4_step22_hkde HK DE AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_gf : g ≠ f := by euclid_apply (helper_2_4_step22_gf g f HK DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step22_adni : ¬(AD.intersectsLine CF) := by euclid_apply (helper_2_4_step22_adni AD CF (by assumption)); (try split_ands) <;> assumption
  have step22_par : formParallelogram h g d f HK DE AD CF := by euclid_apply (helper_2_4_step22_par h g f d HK DE AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- d ≠ f, d ≠ h for the rectangle's corner angle (sides are positive: |a─c| > 0)
  have hac : a ≠ c := by euclid_finish
  have hdh : d ≠ h := by euclid_finish
  have hdf : d ≠ f := by euclid_finish
  -- destructure step22's conjunction into the atoms step24_hf takes
  have heq3 : |(h─g)| = |(g─f)| := hstep22.1.1
  have heq1 : |(g─f)| = |(f─d)| := hstep22.1.2.1
  have heq2 : |(f─d)| = |(d─h)| := hstep22.1.2.2
  have hfdh : ∠ f:d:h = ∟ := hstep22.2.2.2.2
  -- the two square areas
  have step24_hf : Triangle.area △ h:g:f + Triangle.area △ h:f:d = |(a─c)| * |(a─c)| := by euclid_apply (helper_2_4_step24_hf a c h g f d HK DE AD CF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  exact ⟨step24_hf, hstep21⟩

end Elements.Book2
