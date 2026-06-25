import SystemE
import Book.Prop34
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.21: the square CGKB is on CB — area(CGKB) = |c─b|². CGKB is a parallelogram (step9_par) with
   the right angle ∠ c:g:k = ∟ (step18), so by rectangle_area its area
   (△c:g:k + △c:b:k) = |c─b|·|c─g|; and |c─g| = |c─b| (step12, equilateral), giving |c─b|·|c─b|.
   (△c:b:k = △c:k:b by area symmetry.) -/
theorem helper_2_4_step21 (a b c d e g k : Point) (AB CF AD BE HK BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep12 : |(c─g)| = |(g─k)| ∧ |(g─k)| = |(k─b)| ∧ |(k─b)| = |(b─c)|)
    (hstep18 : (∠ k:b:c = ∟) ∧ (∠ b:c:g = ∟) ∧ (∠ c:g:k = ∟) ∧ (∠ g:k:b = ∟)) :
    Triangle.area △ c:g:k + Triangle.area △ c:k:b = |(c─b)| * |(c─b)| := by
  euclid_intros
  -- off-line preamble for the parallelogram CGKB
  have had : a ≠ d := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbd : b ≠ d := fun h => step8_dnab (h ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_par : formParallelogram c b g k AB HK CF BE := by euclid_apply (helper_2_4_step9_par a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  -- |c─g| = |c─b| from the equilateral chain (and distance symmetry)
  have hcgcb : |(c─g)| = |(c─b)| := by euclid_finish
  -- rectangle area: area(CGKB) = |c─b|·|c─g|
  have hrect : Triangle.area △ c:g:k + Triangle.area △ c:b:k = |(c─b)| * |(c─g)| := by
    euclid_apply (rectangle_area c b g k AB HK CF BE)
    euclid_finish
  -- area symmetry △c:b:k = △c:k:b and the length substitution
  rw [hcgcb] at hrect
  euclid_finish

end Elements.Book2
