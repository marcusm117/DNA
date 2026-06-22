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
import Book2.Prop07.step8_ahd
import Book2.Prop07.step4_cgn
import Book2.Prop07.step3_bgd_ss
import Book2.Prop07.step11_dne
import Book2.Prop07.step3_bke
import Book2.Prop07.step3_gnbe
import Book2.Prop07.step13_asd
import Book2.Prop07.step13_asc
import Book2.Prop07.step4_cbde
import Book2.Prop07.step13_csb
import Book2.Prop07.step11_hsd
import Book2.Prop07.step13_bigpar
import Book2.Prop07.step13_parL
import Book2.Prop07.step13_parR
import Book2.Prop07.step11_parDG
import Book2.Prop07.step13_parCF2
import Book2.Prop07.step13_cbf
import Book2.Prop07.step9_tri
import Book2.Prop07.step9_ss
import Book2.Prop07.step9_corr
import Book2.Prop07.step9_iso
import Book2.Prop07.step9_cgb
import Book2.Prop07.step9_bccg
import Book2.Prop07.step13_tile
import Book2.Prop07.step13_adeb
import Book2.Prop07.step13_cfbc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13: the gnomon KLM and the squares BG (=CF) and GD (=DG) are equivalent to the whole square
   ADEB plus CF — the squares on AB and BC. The four pieces AG, CF, DG, GE tile ADEB (step13_tile),
   so the LHS (= AG+GE+CF+CF+DG) = ADEB + CF; with area(ADEB)=|a─b|² (step13_adeb) and area(CF)=|b─c|²
   (step13_cfbc), the LHS equals |a─b|² + |b─c|². -/
theorem helper_2_7_step13 (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
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
    (((Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
        (Triangle.area △ g:f:e + Triangle.area △ g:e:n) +
        (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ c:b:f + Triangle.area △ c:f:g)) +
      (Triangle.area △ d:h:g + Triangle.area △ d:g:n) =
      |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
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
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hgd0 : g ≠ d := by euclid_finish
  have step3_dnhf : ¬(d.onLine HF) := by euclid_apply (helper_2_7_step3_dnhf b d g BD HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_hnde : ¬(h.onLine DE) := by euclid_apply (helper_2_7_step3_hnde a b d g h AB AD HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- line distinctness
  have hADCN : AD ≠ CN := fun hh => step3_cnad (hh ▸ hcCN)
  have hCNBE : CN ≠ BE := fun hh => step3_cnbe (hh ▸ hcCN)
  have hABHF : AB ≠ HF := fun hh => step3_gnab (hh ▸ hgHF)
  have hHFDE : HF ≠ DE := fun hh => step3_hnde (hh ▸ hhHF)
  have hDEAB' : DE ≠ AB := fun hh => step3_dnab (hh ▸ hdDE)
  have hABDE' : AB ≠ DE := fun hh => hDEAB' hh.symm
  have hADBE' : AD ≠ BE := fun hh => step3_anbe (hh ▸ haAD)
  -- non-intersections
  have step3_cfbe : ¬(CN.intersectsLine BE) := by euclid_apply (helper_2_7_step3_cfbe a CN AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_hkde : ¬(HF.intersectsLine DE) := by euclid_apply (helper_2_7_step3_hkde HF DE AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bead : ¬(BE.intersectsLine AD) := by euclid_apply (helper_2_7_step3_bead AD BE (by assumption)); (try split_ands) <;> assumption
  have step3_abde : ¬(AB.intersectsLine DE) := by euclid_apply (helper_2_7_step3_abde AB DE (by assumption)); (try split_ands) <;> assumption
  -- foot betweennesses
  have step8_ahd : between a h d := by euclid_apply (helper_2_7_step8_ahd a b d g h AB HF BD AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_cgn : between c g n := by euclid_apply (helper_2_7_step4_cgn b c d n g AB DE HF BD CN (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bgd_ss : a.sameSide d CN := by euclid_apply (helper_2_7_step3_bgd_ss a b c d AB CN AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step11_dne : between d n e := by euclid_apply (helper_2_7_step11_dne a b c d e n g AB CN AD BE DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_bke : between b f e := by euclid_apply (helper_2_7_step3_bke a b d e g f BE HF DE BD AB CN AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- distinctness of cut points
  have hbf : b ≠ f := fun hh => step3_bnhf (hh ▸ hfHF)
  have step3_gnbe : ¬(g.onLine BE) := by euclid_apply (helper_2_7_step3_gnbe g CN BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hne : n ≠ e := by euclid_finish
  have hgn : g ≠ n := by euclid_finish
  have hgf : g ≠ f := by euclid_finish
  have hbe : b ≠ e := heb.symm
  have hdn : d ≠ n := by euclid_finish
  -- sameSide facts for the parallelograms
  have step13_asd : a.sameSide d BE := by euclid_apply (helper_2_7_step13_asd a d AD BE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_asc : a.sameSide c DE := by euclid_apply (helper_2_7_step13_asc a c AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step4_cbde : c.sameSide b DE := by euclid_apply (helper_2_7_step4_cbde c b AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_csb : c.sameSide b HF := by euclid_apply (helper_2_7_step13_csb c b AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the four parallelograms (whole + left + right for the tiling, CBFG for the area)
  have step11_hsd : h.sameSide d CN := by euclid_apply (helper_2_7_step11_hsd h d AD CN (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_bigpar : formParallelogram a b d e AB DE AD BE := by euclid_apply (helper_2_7_step13_bigpar a b d e AB DE AD BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_parL : formParallelogram a d c n AD CN AB DE := by euclid_apply (helper_2_7_step13_parL a d c n AD CN AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_parR : formParallelogram c n b e CN BE AB DE := by euclid_apply (helper_2_7_step13_parR c n b e CN BE AB DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step11_parDG : formParallelogram h g d n HF DE AD CN := by euclid_apply (helper_2_7_step11_parDG h g d n HF DE AD CN (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_parCF2 : formParallelogram c g b f CN BE AB HF := by euclid_apply (helper_2_7_step13_parCF2 c g b f CN BE AB HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the right angle and equilateral side for CF
  have step13_cbf : ∠ c:b:f = ∟ := by euclid_apply (helper_2_7_step13_cbf a b c e f AB BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_tri : formTriangle c g b CN BD AB := by euclid_apply (helper_2_7_step9_tri a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_ss : c.sameSide a BD := by euclid_apply (helper_2_7_step9_ss a b c d AB BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_corr : ∠ c:g:b = ∠ a:d:b := by euclid_apply (helper_2_7_step9_corr a b c d g CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_iso : ∠ a:d:b = ∠ a:b:d := by euclid_apply (helper_2_7_step9_iso a b d AB AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_cgb : ∠ c:g:b = ∠ g:b:c := by euclid_apply (helper_2_7_step9_cgb a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_bccg : |(b─c)| = |(c─g)| := by euclid_apply (helper_2_7_step9_bccg a b c d g AB CN AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  -- the tiling and the two square areas
  have step13_tile : (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      + (Triangle.area △ d:h:g + Triangle.area △ d:g:n)
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b := by euclid_apply (helper_2_7_step13_tile a b c d e n g h f AB CN AD BE HF BD DE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_adeb : Triangle.area △ a:d:e + Triangle.area △ a:e:b = |(a─b)| * |(a─b)| := by euclid_apply (helper_2_7_step13_adeb a b d e AB DE AD BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_cfbc : Triangle.area △ c:b:f + Triangle.area △ c:f:g = |(b─c)| * |(b─c)| := by euclid_apply (helper_2_7_step13_cfbc c g b f CN BE AB HF (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
