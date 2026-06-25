import SystemE
import Book2.Prop07.step3_dnab
import Book2.Prop07.step3_bgd
import Book2.Prop07.step3_anbe
import Book2.Prop07.step3_cnbe
import Book2.Prop07.step3_cab
import Book2.Prop07.step3_gnab
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_cnad
import Book2.Prop07.step9_tri
import Book2.Prop07.step9_ss
import Book2.Prop07.step9_corr
import Book2.Prop07.step9_iso
import Book2.Prop07.step9_cgb
import Book2.Prop07.step9_bccg
import Book2.Prop07.step3_cfbe
import Book2.Prop07.step9_csg
import Book2.Prop07.step9_parCF
import Book2.Prop07.step9_cgbf
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- BF = BC (shared core of sentence 2.7.9, also used by 2.7.8). In the square CF (= CBFG) the side
   BF equals the opposite side CG (step9_cgbf, via Prop.~1.34), and CG = CB by the isosceles argument
   on triangle CGB (step9_corr/iso/cgb/bccg: the base angles ∠cgb and ∠gbc are equal, so
   |b─c| = |c─g|). Hence |b─f| = |c─g| = |b─c|. -/
theorem helper_2_7_step9_bfbc (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    |(b─f)| = |(b─c)| := by
  euclid_intros
  have had : a ≠ d := by euclid_finish
  have step3_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_7_step3_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbd : b ≠ d := fun hh => step3_dnab (hh ▸ hbAB)
  have step3_bgd : between b g d := by euclid_apply (helper_2_7_step3_bgd a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hbg : b ≠ g := (between_symm b g d step3_bgd).2.1
  have hgd : g ≠ d := ((between_symm d g b (between_symm b g d step3_bgd).1).2.1).symm
  have step3_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_7_step3_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step3_cnbe : ¬(c.onLine BE) := by euclid_apply (helper_2_7_step3_cnbe a b c e AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step3_cab : c.onLine AB := by euclid_apply (helper_2_7_step3_cab a b c AB (by assumption) (by assumption) (by assumption))
  have step3_gnab : ¬(g.onLine AB) := by euclid_apply (helper_2_7_step3_gnab a b d g AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption))
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_7_step3_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have step9_tri : formTriangle c g b CN BD AB := by euclid_apply (helper_2_7_step9_tri a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_ss : c.sameSide a BD := by euclid_apply (helper_2_7_step9_ss a b c d AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_corr : ∠ c:g:b = ∠ a:d:b := by euclid_apply (helper_2_7_step9_corr a b c d g CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_iso : ∠ a:d:b = ∠ a:b:d := by euclid_apply (helper_2_7_step9_iso a b d AB AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_cgb : ∠ c:g:b = ∠ g:b:c := by euclid_apply (helper_2_7_step9_cgb a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_bccg : |(b─c)| = |(c─g)| := by euclid_apply (helper_2_7_step9_bccg a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step3_cfbe : ¬(CN.intersectsLine BE) := by euclid_apply (helper_2_7_step3_cfbe a CN AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_csg : c.sameSide g BE := by euclid_apply (helper_2_7_step9_csg c g CN BE (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_parCF : formParallelogram c b g f AB HF CN BE := by euclid_apply (helper_2_7_step9_parCF c b g f AB HF CN BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
  have step9_cgbf : |(c─g)| = |(b─f)| := by euclid_apply (helper_2_7_step9_cgbf c b g f AB HF CN BE BD (by assumption) (by assumption) (by assumption) (by assumption))
  euclid_finish

end Elements.Book2
