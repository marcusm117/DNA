import SystemE
import Book2.Prop07.step3_dnab
import Book2.Prop07.step3_bgd
import Book2.Prop07.step3_gnab
import Book2.Prop07.step3_cnbe
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_cnad
import Book2.Prop07.step3_anbe
import Book2.Prop07.step3_hnde
import Book2.Prop07.step3_cab
import Book2.Prop07.step3_cfbe
import Book2.Prop07.step3_hkde
import Book2.Prop07.step8_ahd
import Book2.Prop07.step3_bgd_ss
import Book2.Prop07.step11_dne
import Book2.Prop07.step4_ahbe
import Book2.Prop07.step8_hsa
import Book2.Prop07.step8_parAF2
import Book2.Prop07.step4_parAF
import Book2.Prop07.step8_lens
import Book2.Prop07.step9_bfbc
import Book2.Prop07.step11_dhac
import Book2.Prop07.step3_ahcf
import Book2.Prop07.step3_paracgh
import Book2.Prop07.step11_hgac
import Book2.Prop07.step11_hsd
import Book2.Prop07.step11_parDG
import Book2.Prop07.step11_rangle
import Book2.Prop07.step11_rect
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.11: DG (= the bottom-left square DHGN) is the square on AC — area(DHGN) = |a─c|².
   DHGN is a rectangle (step11_parDG) with the right angle ∠h:d:n = ∟ (= ∠a:d:e), so by
   rectangle_area its area is |h─d|·|h─g| (step11_rect). Its sides equal AC: |h─d| = |a─c|
   (step11_dhac, since |a─h| = |b─f| = |b─c| and |a─d| = |a─b| = |a─c|+|c─b|) and |a─c| = |h─g|
   (step11_hgac, opposite sides of rectangle ACGH). Hence area = |a─c|·|a─c|. -/
theorem helper_2_7_step11 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(a─c)| * |(a─c)| := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_7_step3_dnab a b d AB (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)))
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have step3_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_7_step3_gnab a b d g AB BD (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b ≠ g; assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)))
  have step3_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_7_step3_cnbe a b c e AB BE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show ¬(g.onLine AB); assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)))
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have hfb : f ≠ b := fun hh => hbf hh.symm
  have step3_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_7_step3_cnad a b c d AB AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)))
  have step3_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_7_step3_anbe a b e BE (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have step3_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_7_step3_hnde a b d g h AB AD HF BD DE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(d.onLine AB); assumption)) (by euclid_assumption "" (show between b g d; assumption)) (by euclid_assumption "" (show ¬(b.onLine HF); assumption)))
  have step3_cab : c.onLine AB := by euclid_apply (helper_2_7_step3_cab a b c AB (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)))
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  -- non-intersections
  have step3_cfbe : ¬(CN.intersectsLine BE) := by euclid_apply (helper_2_7_step3_cfbe a CN AD BE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show ¬(a.onLine BE); assumption)) (by euclid_assumption "" (show CN ≠ BE; assumption)) (by euclid_assumption "" (show AD ≠ CN; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step3_hkde : ¬(HF.intersectsLine DE) := by euclid_apply (helper_2_7_step3_hkde HF DE AB (by euclid_assumption "" (show HF ≠ DE; assumption)) (by euclid_assumption "" (show DE ≠ AB; assumption)) (by euclid_assumption "" (show AB ≠ HF; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)))
  -- foot betweennesses
  have step8_ahd : between a h d := by euclid_apply (helper_2_7_step8_ahd a b d g h AB HF BD AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show AB ≠ HF; assumption)) (by euclid_assumption "" (show between b g d; assumption)))
  have step3_bgd_ss : a.sameSide d CN := by euclid_apply (helper_2_7_step3_bgd_ss a b c d AB CN AD (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)))
  have step11_dne : between d n e := by euclid_apply (helper_2_7_step11_dne a b c d e n g AB CN AD BE DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show n.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show n.onLine DE; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine BE); assumption)) (by euclid_assumption "" (show AD ≠ CN; assumption)) (by euclid_assumption "" (show CN ≠ BE; assumption)) (by euclid_assumption "" (show a.sameSide d CN; assumption)))
  have hgn : g ≠ n := by euclid_finish
  -- side lengths
  have step4_ahbe : a.sameSide h BE := by euclid_apply (helper_2_7_step4_ahbe a h AD BE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ BE; assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step8_hsa : h.sameSide a BE := by euclid_apply (helper_2_7_step8_hsa h a AD BE (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ BE; assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)))
  have step8_parAF2 : formParallelogram h f a b HF AB AD BE := by euclid_apply (helper_2_7_step8_parAF2 h f a b HF AB AD BE (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show f.onLine HF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show h.sameSide a BE; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)))
  have step4_parAF : formParallelogram a b h f AB HF AD BE := by euclid_apply (helper_2_7_step4_parAF a b h f AB HF AD BE (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show f.onLine HF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show a.sameSide h BE; assumption)) (by euclid_assumption "" (show b ≠ f; assumption)))
  have step8_lens : |(a─b)| = |(h─f)| ∧ |(a─h)| = |(b─f)| := by euclid_apply (helper_2_7_step8_lens a b h f AB HF AD BE (by euclid_assumption "" (show formParallelogram a b h f AB HF AD BE; assumption)))
  have step9_bfbc : |(b─f)| = |(b─c)| := by euclid_apply (helper_2_7_step9_bfbc a b c d e n g h f AB CN AD BE HF BD DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show n.onLine CN; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show f.onLine BE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show n.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show f.onLine HF; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(AD.intersectsLine BE); assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show ¬(DE.intersectsLine AB); assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(a─b)|; assumption)) (by euclid_assumption "" (show ∠ b:a:d = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:e = ∟; assumption)))
  have hahbc : |(a─h)| = |(b─c)| := by
    rw [step8_lens.2, step9_bfbc]
  have step11_dhac : |(d─h)| = |(a─c)| := by euclid_apply (helper_2_7_step11_dhac a b c d h (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show |(a─d)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(b─c)|; assumption)))
  -- the rectangle ACGH for |a─c| = |h─g|
  have step3_ahcf : a.sameSide h CN := by euclid_apply (helper_2_7_step3_ahcf a h AD CN (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CN; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)))
  have hcg : c ≠ g := fun hh => step3_gnab (hh ▸ step3_cab)
  have step3_paracgh : formParallelogram a c h g AB HF AD CN := by euclid_apply (helper_2_7_step3_paracgh a c h g AB HF AD CN (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show c.onLine CN; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine AB); assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show a.sameSide h CN; assumption)) (by euclid_assumption "" (show c ≠ g; assumption)))
  have step11_hgac : |(a─c)| = |(h─g)| := by euclid_apply (helper_2_7_step11_hgac a c h g AB HF AD CN (by euclid_assumption "" (show formParallelogram a c h g AB HF AD CN; assumption)))
  -- the square DHGN and its area
  have step11_hsd : h.sameSide d CN := by euclid_apply (helper_2_7_step11_hsd h d AD CN (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show AD ≠ CN; assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)))
  have step11_parDG : formParallelogram h g d n HF DE AD CN := by euclid_apply (helper_2_7_step11_parDG h g d n HF DE AD CN (by euclid_assumption "" (show h.onLine HF; assumption)) (by euclid_assumption "" (show g.onLine HF; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show n.onLine DE; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show g.onLine CN; assumption)) (by euclid_assumption "" (show n.onLine CN; assumption)) (by euclid_assumption "" (show ¬(HF.intersectsLine DE); assumption)) (by euclid_assumption "" (show ¬(CN.intersectsLine AD); assumption)) (by euclid_assumption "" (show h.sameSide d CN; assumption)) (by euclid_assumption "" (show g ≠ n; assumption)))
  have step11_rangle : ∠ h:d:n = ∟ := by euclid_apply (helper_2_7_step11_rangle a d e h n AD DE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show h.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show n.onLine DE; assumption)) (by euclid_assumption "" (show ∠ a:d:e = ∟; assumption)) (by euclid_assumption "" (show between a h d; assumption)) (by euclid_assumption "" (show between d n e; assumption)))
  have step11_rect : Triangle.area △ d:h:g + Triangle.area △ d:g:n = |(h─d)| * |(h─g)| := by euclid_apply (helper_2_7_step11_rect h g d n HF DE AD CN (by euclid_assumption "" (show formParallelogram h g d n HF DE AD CN; assumption)) (by euclid_assumption "" (show ∠ h:d:n = ∟; assumption)))
  euclid_finish

end Elements.Book2
